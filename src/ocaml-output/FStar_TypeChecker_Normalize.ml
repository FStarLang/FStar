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
  fun uu___135_233  ->
    match uu___135_233 with
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
    match projectee with | Arg _0 -> true | uu____375 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____399 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____423 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____450 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____479 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____518 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____541 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____563 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____592 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____619 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____631 =
      let uu____632 = FStar_Syntax_Util.un_uinst t in
      uu____632.FStar_Syntax_Syntax.n in
    match uu____631 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_refl_embed_lid
    | uu____636 -> false
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____676 = FStar_ST.read r in
  match uu____676 with
  | Some uu____681 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____690 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____690 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___136_695  ->
    match uu___136_695 with
    | Arg (c,uu____697,uu____698) ->
        let uu____699 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____699
    | MemoLazy uu____700 -> "MemoLazy"
    | Abs (uu____704,bs,uu____706,uu____707,uu____708) ->
        let uu____715 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____715
    | UnivArgs uu____720 -> "UnivArgs"
    | Match uu____724 -> "Match"
    | App (t,uu____729,uu____730) ->
        let uu____731 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____731
    | Meta (m,uu____733) -> "Meta"
    | Let uu____734 -> "Let"
    | Steps (uu____739,uu____740,uu____741) -> "Steps"
    | Debug t ->
        let uu____747 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____747
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____753 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____753 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____767 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____767 then f () else ()
let is_empty uu___137_776 =
  match uu___137_776 with | [] -> true | uu____778 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____796 ->
      let uu____797 =
        let uu____798 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____798 in
      failwith uu____797
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
          let uu____829 =
            FStar_List.fold_left
              (fun uu____838  ->
                 fun u1  ->
                   match uu____838 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____853 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____853 with
                        | (k_u,n1) ->
                            let uu____862 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____862
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____829 with
          | (uu____872,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____888 = FStar_List.nth env x in
                 match uu____888 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____891 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____895 ->
                   let uu____896 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____896
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____900 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____903 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____908 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____908 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____919 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____919 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____924 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____927 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____927 with
                                  | (uu____930,m) -> n1 <= m)) in
                        if uu____924 then rest1 else us1
                    | uu____934 -> us1)
               | uu____937 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____940 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____940 in
        let uu____942 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____942
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____944 = aux u in
           match uu____944 with
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
          (fun uu____1041  ->
             let uu____1042 = FStar_Syntax_Print.tag_of_term t in
             let uu____1043 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1042
               uu____1043);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1044 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1047 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1068 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1069 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1070 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1071 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1081 =
                    let uu____1082 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1082 in
                  mk uu____1081 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1089 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1089
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1091 = lookup_bvar env x in
                  (match uu____1091 with
                   | Univ uu____1092 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1096) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1164 = closures_as_binders_delayed cfg env bs in
                  (match uu____1164 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1184 =
                         let uu____1185 =
                           let uu____1200 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1200) in
                         FStar_Syntax_Syntax.Tm_abs uu____1185 in
                       mk uu____1184 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1230 = closures_as_binders_delayed cfg env bs in
                  (match uu____1230 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1261 =
                    let uu____1268 =
                      let uu____1272 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1272] in
                    closures_as_binders_delayed cfg env uu____1268 in
                  (match uu____1261 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1286 =
                         let uu____1287 =
                           let uu____1292 =
                             let uu____1293 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1293
                               FStar_Pervasives.fst in
                           (uu____1292, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1287 in
                       mk uu____1286 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1361 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1361
                    | FStar_Util.Inr c ->
                        let uu____1375 = close_comp cfg env c in
                        FStar_Util.Inr uu____1375 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1390 =
                    let uu____1391 =
                      let uu____1409 = closure_as_term_delayed cfg env t11 in
                      (uu____1409, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1391 in
                  mk uu____1390 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1447 =
                    let uu____1448 =
                      let uu____1453 = closure_as_term_delayed cfg env t' in
                      let uu____1456 =
                        let uu____1457 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1457 in
                      (uu____1453, uu____1456) in
                    FStar_Syntax_Syntax.Tm_meta uu____1448 in
                  mk uu____1447 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1499 =
                    let uu____1500 =
                      let uu____1505 = closure_as_term_delayed cfg env t' in
                      let uu____1508 =
                        let uu____1509 =
                          let uu____1514 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1514) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1509 in
                      (uu____1505, uu____1508) in
                    FStar_Syntax_Syntax.Tm_meta uu____1500 in
                  mk uu____1499 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1533 =
                    let uu____1534 =
                      let uu____1539 = closure_as_term_delayed cfg env t' in
                      let uu____1542 =
                        let uu____1543 =
                          let uu____1549 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1549) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1543 in
                      (uu____1539, uu____1542) in
                    FStar_Syntax_Syntax.Tm_meta uu____1534 in
                  mk uu____1533 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1562 =
                    let uu____1563 =
                      let uu____1568 = closure_as_term_delayed cfg env t' in
                      (uu____1568, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1563 in
                  mk uu____1562 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1589  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1600 -> body
                    | FStar_Util.Inl uu____1601 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___150_1603 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1603.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1603.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1603.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1610,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1634  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1639 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1639
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1643  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___151_1646 = lb in
                    let uu____1647 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1650 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1646.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1646.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1647;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1646.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1650
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1661  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1716 =
                    match uu____1716 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1762 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1778 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1812  ->
                                        fun uu____1813  ->
                                          match (uu____1812, uu____1813) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1878 =
                                                norm_pat env3 p1 in
                                              (match uu____1878 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1778 with
                               | (pats1,env3) ->
                                   ((let uu___152_1944 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_1944.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_1944.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___153_1958 = x in
                                let uu____1959 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_1958.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_1958.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1959
                                } in
                              ((let uu___154_1965 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_1965.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_1965.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___155_1970 = x in
                                let uu____1971 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_1970.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_1970.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1971
                                } in
                              ((let uu___156_1977 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_1977.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_1977.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___157_1987 = x in
                                let uu____1988 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_1987.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_1987.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1988
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___158_1995 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_1995.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_1995.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1998 = norm_pat env1 pat in
                        (match uu____1998 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2022 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2022 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2027 =
                    let uu____2028 =
                      let uu____2044 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2044) in
                    FStar_Syntax_Syntax.Tm_match uu____2028 in
                  mk uu____2027 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2097 -> closure_as_term cfg env t
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
        | uu____2113 ->
            FStar_List.map
              (fun uu____2123  ->
                 match uu____2123 with
                 | (x,imp) ->
                     let uu____2138 = closure_as_term_delayed cfg env x in
                     (uu____2138, imp)) args
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
        let uu____2150 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2174  ->
                  fun uu____2175  ->
                    match (uu____2174, uu____2175) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___159_2219 = b in
                          let uu____2220 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___159_2219.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___159_2219.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2220
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2150 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2267 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2279 = closure_as_term_delayed cfg env t in
                 let uu____2280 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2279 uu____2280
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2290 = closure_as_term_delayed cfg env t in
                 let uu____2291 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2290 uu____2291
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
                        (fun uu___138_2307  ->
                           match uu___138_2307 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2311 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2311
                           | f -> f)) in
                 let uu____2315 =
                   let uu___160_2316 = c1 in
                   let uu____2317 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2317;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___160_2316.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2315)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___139_2321  ->
            match uu___139_2321 with
            | FStar_Syntax_Syntax.DECREASES uu____2322 -> false
            | uu____2325 -> true))
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
            let uu____2353 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2353
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2370 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2370
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2396 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2420 =
      let uu____2421 =
        let uu____2427 = FStar_Util.string_of_int i in (uu____2427, None) in
      FStar_Const.Const_int uu____2421 in
    const_as_tm uu____2420 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2454 =
    match uu____2454 with
    | (a,uu____2459) ->
        let uu____2461 =
          let uu____2462 = FStar_Syntax_Subst.compress a in
          uu____2462.FStar_Syntax_Syntax.n in
        (match uu____2461 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2472 = FStar_Util.int_of_string i in Some uu____2472
         | uu____2473 -> None) in
  let arg_as_bounded_int uu____2482 =
    match uu____2482 with
    | (a,uu____2489) ->
        let uu____2493 =
          let uu____2494 = FStar_Syntax_Subst.compress a in
          uu____2494.FStar_Syntax_Syntax.n in
        (match uu____2493 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2501;
                FStar_Syntax_Syntax.pos = uu____2502;
                FStar_Syntax_Syntax.vars = uu____2503;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2505;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2506;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2507;_},uu____2508)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2539 =
               let uu____2542 = FStar_Util.int_of_string i in
               (fv1, uu____2542) in
             Some uu____2539
         | uu____2545 -> None) in
  let arg_as_bool uu____2554 =
    match uu____2554 with
    | (a,uu____2559) ->
        let uu____2561 =
          let uu____2562 = FStar_Syntax_Subst.compress a in
          uu____2562.FStar_Syntax_Syntax.n in
        (match uu____2561 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2567 -> None) in
  let arg_as_char uu____2574 =
    match uu____2574 with
    | (a,uu____2579) ->
        let uu____2581 =
          let uu____2582 = FStar_Syntax_Subst.compress a in
          uu____2582.FStar_Syntax_Syntax.n in
        (match uu____2581 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2587 -> None) in
  let arg_as_string uu____2594 =
    match uu____2594 with
    | (a,uu____2599) ->
        let uu____2601 =
          let uu____2602 = FStar_Syntax_Subst.compress a in
          uu____2602.FStar_Syntax_Syntax.n in
        (match uu____2601 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2607)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2610 -> None) in
  let arg_as_list f uu____2631 =
    match uu____2631 with
    | (a,uu____2640) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2659 -> None
          | (Some x)::xs ->
              let uu____2669 = sequence xs in
              (match uu____2669 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2680 = FStar_Syntax_Util.list_elements a in
        (match uu____2680 with
         | None  -> None
         | Some elts ->
             let uu____2690 =
               FStar_List.map
                 (fun x  ->
                    let uu____2695 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2695) elts in
             sequence uu____2690) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2725 = f a in Some uu____2725
    | uu____2726 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2765 = f a0 a1 in Some uu____2765
    | uu____2766 -> None in
  let unary_op as_a f r args =
    let uu____2810 = FStar_List.map as_a args in lift_unary (f r) uu____2810 in
  let binary_op as_a f r args =
    let uu____2860 = FStar_List.map as_a args in lift_binary (f r) uu____2860 in
  let as_primitive_step uu____2877 =
    match uu____2877 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2915 = f x in int_as_const r uu____2915) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2938 = f x y in int_as_const r uu____2938) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2955 = f x in bool_as_const r uu____2955) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2978 = f x y in bool_as_const r uu____2978) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3001 = f x y in string_as_const r uu____3001) in
  let list_of_string' rng s =
    let name l =
      let uu____3015 =
        let uu____3016 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3016 in
      mk uu____3015 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3026 =
      let uu____3028 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3028 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3026 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3082 = arg_as_string a1 in
        (match uu____3082 with
         | Some s1 ->
             let uu____3086 = arg_as_list arg_as_string a2 in
             (match uu____3086 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3094 = string_as_const rng r in Some uu____3094
              | uu____3095 -> None)
         | uu____3098 -> None)
    | uu____3100 -> None in
  let string_of_int1 rng i =
    let uu____3111 = FStar_Util.string_of_int i in
    string_as_const rng uu____3111 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3127 = FStar_Util.string_of_int i in
    string_as_const rng uu____3127 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
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
                        let uu____3246 =
                          let uu____3256 =
                            let uu____3266 =
                              let uu____3276 =
                                let uu____3286 =
                                  let uu____3296 =
                                    let uu____3306 =
                                      let uu____3316 =
                                        let uu____3325 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3325, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3331 =
                                        let uu____3341 =
                                          let uu____3350 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3350, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3357 =
                                          let uu____3367 =
                                            let uu____3379 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3379,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3367] in
                                        uu____3341 :: uu____3357 in
                                      uu____3316 :: uu____3331 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3306 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3296 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3286 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3276 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3266 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3256 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3246 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3236 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3226 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3216 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3206 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3196 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3186 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3176 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3166 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3156 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3146 in
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
      let uu____3703 =
        let uu____3704 =
          let uu____3705 = FStar_Syntax_Syntax.as_arg c in [uu____3705] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3704 in
      uu____3703 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3729 =
              let uu____3738 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3738, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3747  ->
                        fun uu____3748  ->
                          match (uu____3747, uu____3748) with
                          | ((int_to_t1,x),(uu____3759,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3765 =
              let uu____3775 =
                let uu____3784 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3784, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3793  ->
                          fun uu____3794  ->
                            match (uu____3793, uu____3794) with
                            | ((int_to_t1,x),(uu____3805,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3811 =
                let uu____3821 =
                  let uu____3830 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3830, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3839  ->
                            fun uu____3840  ->
                              match (uu____3839, uu____3840) with
                              | ((int_to_t1,x),(uu____3851,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3821] in
              uu____3775 :: uu____3811 in
            uu____3729 :: uu____3765)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3917)::(a1,uu____3919)::(a2,uu____3921)::[] ->
        let uu____3950 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3950 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3952 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3952
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3957 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3957
         | uu____3962 -> None)
    | uu____3963 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3976)::(a1,uu____3978)::(a2,uu____3980)::[] ->
        let uu____4009 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4009 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4013 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4013.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4013.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4013.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4020 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4020.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4020.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4020.FStar_Syntax_Syntax.vars)
                })
         | uu____4025 -> None)
    | (_typ,uu____4027)::uu____4028::(a1,uu____4030)::(a2,uu____4032)::[] ->
        let uu____4069 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4069 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4073 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4073.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4073.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4073.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4080 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4080.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4080.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4080.FStar_Syntax_Syntax.vars)
                })
         | uu____4085 -> None)
    | uu____4086 -> failwith "Unexpected number of arguments" in
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
      let uu____4097 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4097
      then tm
      else
        (let uu____4099 = FStar_Syntax_Util.head_and_args tm in
         match uu____4099 with
         | (head1,args) ->
             let uu____4125 =
               let uu____4126 = FStar_Syntax_Util.un_uinst head1 in
               uu____4126.FStar_Syntax_Syntax.n in
             (match uu____4125 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4130 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4130 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4142 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4142 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4145 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___163_4152 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4152.tcenv);
           delta_level = (uu___163_4152.delta_level);
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
        let uu___164_4174 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4174.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4174.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4174.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4193 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4221 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4221
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4224;
                     FStar_Syntax_Syntax.pos = uu____4225;
                     FStar_Syntax_Syntax.vars = uu____4226;_},uu____4227);
                FStar_Syntax_Syntax.tk = uu____4228;
                FStar_Syntax_Syntax.pos = uu____4229;
                FStar_Syntax_Syntax.vars = uu____4230;_},args)
             ->
             let uu____4250 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4250
             then
               let uu____4251 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4251 with
                | (Some (true ),uu____4284)::(uu____4285,(arg,uu____4287))::[]
                    -> arg
                | (uu____4328,(arg,uu____4330))::(Some (true ),uu____4331)::[]
                    -> arg
                | (Some (false ),uu____4372)::uu____4373::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4411::(Some (false ),uu____4412)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4450 -> tm1)
             else
               (let uu____4460 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4460
                then
                  let uu____4461 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4461 with
                  | (Some (true ),uu____4494)::uu____4495::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4533::(Some (true ),uu____4534)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4572)::(uu____4573,(arg,uu____4575))::[]
                      -> arg
                  | (uu____4616,(arg,uu____4618))::(Some (false ),uu____4619)::[]
                      -> arg
                  | uu____4660 -> tm1
                else
                  (let uu____4670 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4670
                   then
                     let uu____4671 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4671 with
                     | uu____4704::(Some (true ),uu____4705)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4743)::uu____4744::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4782)::(uu____4783,(arg,uu____4785))::[]
                         -> arg
                     | uu____4826 -> tm1
                   else
                     (let uu____4836 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4836
                      then
                        let uu____4837 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4837 with
                        | (Some (true ),uu____4870)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4894)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4918 -> tm1
                      else
                        (let uu____4928 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4928
                         then
                           match args with
                           | (t,uu____4930)::[] ->
                               let uu____4943 =
                                 let uu____4944 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4944.FStar_Syntax_Syntax.n in
                               (match uu____4943 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4947::[],body,uu____4949) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4975 -> tm1)
                                | uu____4977 -> tm1)
                           | (uu____4978,Some (FStar_Syntax_Syntax.Implicit
                              uu____4979))::(t,uu____4981)::[] ->
                               let uu____5008 =
                                 let uu____5009 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5009.FStar_Syntax_Syntax.n in
                               (match uu____5008 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5012::[],body,uu____5014) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5040 -> tm1)
                                | uu____5042 -> tm1)
                           | uu____5043 -> tm1
                         else
                           (let uu____5050 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5050
                            then
                              match args with
                              | (t,uu____5052)::[] ->
                                  let uu____5065 =
                                    let uu____5066 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5066.FStar_Syntax_Syntax.n in
                                  (match uu____5065 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5069::[],body,uu____5071) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5097 -> tm1)
                                   | uu____5099 -> tm1)
                              | (uu____5100,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5101))::
                                  (t,uu____5103)::[] ->
                                  let uu____5130 =
                                    let uu____5131 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5131.FStar_Syntax_Syntax.n in
                                  (match uu____5130 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5134::[],body,uu____5136) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5162 -> tm1)
                                   | uu____5164 -> tm1)
                              | uu____5165 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5173;
                FStar_Syntax_Syntax.pos = uu____5174;
                FStar_Syntax_Syntax.vars = uu____5175;_},args)
             ->
             let uu____5191 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5191
             then
               let uu____5192 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5192 with
                | (Some (true ),uu____5225)::(uu____5226,(arg,uu____5228))::[]
                    -> arg
                | (uu____5269,(arg,uu____5271))::(Some (true ),uu____5272)::[]
                    -> arg
                | (Some (false ),uu____5313)::uu____5314::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5352::(Some (false ),uu____5353)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5391 -> tm1)
             else
               (let uu____5401 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5401
                then
                  let uu____5402 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5402 with
                  | (Some (true ),uu____5435)::uu____5436::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5474::(Some (true ),uu____5475)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5513)::(uu____5514,(arg,uu____5516))::[]
                      -> arg
                  | (uu____5557,(arg,uu____5559))::(Some (false ),uu____5560)::[]
                      -> arg
                  | uu____5601 -> tm1
                else
                  (let uu____5611 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5611
                   then
                     let uu____5612 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5612 with
                     | uu____5645::(Some (true ),uu____5646)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5684)::uu____5685::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5723)::(uu____5724,(arg,uu____5726))::[]
                         -> arg
                     | uu____5767 -> tm1
                   else
                     (let uu____5777 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5777
                      then
                        let uu____5778 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5778 with
                        | (Some (true ),uu____5811)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5835)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5859 -> tm1
                      else
                        (let uu____5869 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5869
                         then
                           match args with
                           | (t,uu____5871)::[] ->
                               let uu____5884 =
                                 let uu____5885 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5885.FStar_Syntax_Syntax.n in
                               (match uu____5884 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5888::[],body,uu____5890) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5916 -> tm1)
                                | uu____5918 -> tm1)
                           | (uu____5919,Some (FStar_Syntax_Syntax.Implicit
                              uu____5920))::(t,uu____5922)::[] ->
                               let uu____5949 =
                                 let uu____5950 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5950.FStar_Syntax_Syntax.n in
                               (match uu____5949 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5953::[],body,uu____5955) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5981 -> tm1)
                                | uu____5983 -> tm1)
                           | uu____5984 -> tm1
                         else
                           (let uu____5991 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5991
                            then
                              match args with
                              | (t,uu____5993)::[] ->
                                  let uu____6006 =
                                    let uu____6007 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6007.FStar_Syntax_Syntax.n in
                                  (match uu____6006 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6010::[],body,uu____6012) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6038 -> tm1)
                                   | uu____6040 -> tm1)
                              | (uu____6041,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6042))::
                                  (t,uu____6044)::[] ->
                                  let uu____6071 =
                                    let uu____6072 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6072.FStar_Syntax_Syntax.n in
                                  (match uu____6071 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6075::[],body,uu____6077) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6103 -> tm1)
                                   | uu____6105 -> tm1)
                              | uu____6106 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6113 -> tm1)
let is_norm_request hd1 args =
  let uu____6128 =
    let uu____6132 =
      let uu____6133 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6133.FStar_Syntax_Syntax.n in
    (uu____6132, args) in
  match uu____6128 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6138::uu____6139::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6142::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6144 -> false
let get_norm_request args =
  match args with
  | uu____6163::(tm,uu____6165)::[] -> tm
  | (tm,uu____6175)::[] -> tm
  | uu____6180 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6187  ->
    match uu___140_6187 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6189;
           FStar_Syntax_Syntax.pos = uu____6190;
           FStar_Syntax_Syntax.vars = uu____6191;_},uu____6192,uu____6193))::uu____6194
        -> true
    | uu____6200 -> false
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
            (fun uu____6315  ->
               let uu____6316 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6317 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6318 =
                 let uu____6319 =
                   let uu____6321 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6321 in
                 stack_to_string uu____6319 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6316
                 uu____6317 uu____6318);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6333 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6354 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6363 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6364 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6365;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6366;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6371;
                 FStar_Syntax_Syntax.fv_delta = uu____6372;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6376;
                 FStar_Syntax_Syntax.fv_delta = uu____6377;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6378);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6411 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6411.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6411.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6411.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6437 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6437) && (is_norm_request hd1 args))
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
                 let uu___166_6450 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6450.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6450.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6455;
                  FStar_Syntax_Syntax.pos = uu____6456;
                  FStar_Syntax_Syntax.vars = uu____6457;_},a1::a2::rest)
               ->
               let uu____6491 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6491 with
                | (hd1,uu____6502) ->
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
                    (FStar_Const.Const_reflect uu____6557);
                  FStar_Syntax_Syntax.tk = uu____6558;
                  FStar_Syntax_Syntax.pos = uu____6559;
                  FStar_Syntax_Syntax.vars = uu____6560;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6583 = FStar_List.tl stack1 in
               norm cfg env uu____6583 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6586;
                  FStar_Syntax_Syntax.pos = uu____6587;
                  FStar_Syntax_Syntax.vars = uu____6588;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6611 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6611 with
                | (reify_head,uu____6622) ->
                    let a1 =
                      let uu____6638 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6638 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6641);
                            FStar_Syntax_Syntax.tk = uu____6642;
                            FStar_Syntax_Syntax.pos = uu____6643;
                            FStar_Syntax_Syntax.vars = uu____6644;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6669 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6677 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6677
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6684 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6684
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6687 =
                      let uu____6691 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6691, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6687 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6700  ->
                         match uu___141_6700 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6703 =
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
                 if uu____6703 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6707 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6707 in
                  let uu____6708 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6708 with
                  | None  ->
                      (log cfg
                         (fun uu____6719  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6725  ->
                            let uu____6726 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6727 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6726 uu____6727);
                       (let t3 =
                          let uu____6729 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6729
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
                          | (UnivArgs (us',uu____6741))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6754 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6755 ->
                              let uu____6756 =
                                let uu____6757 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6757 in
                              failwith uu____6756
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6764 = lookup_bvar env x in
               (match uu____6764 with
                | Univ uu____6765 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6780 = FStar_ST.read r in
                      (match uu____6780 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6799  ->
                                 let uu____6800 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6801 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6800
                                   uu____6801);
                            (let uu____6802 =
                               let uu____6803 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6803.FStar_Syntax_Syntax.n in
                             match uu____6802 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6806 ->
                                 norm cfg env2 stack1 t'
                             | uu____6821 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6854)::uu____6855 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6860)::uu____6861 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6867,uu____6868))::stack_rest ->
                    (match c with
                     | Univ uu____6871 -> norm cfg (c :: env) stack_rest t1
                     | uu____6872 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6875::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6888  ->
                                         let uu____6889 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6889);
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
                                           (fun uu___142_6903  ->
                                              match uu___142_6903 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6904 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6906  ->
                                         let uu____6907 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6907);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6918  ->
                                         let uu____6919 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6919);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6920 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6927 ->
                                   let cfg1 =
                                     let uu___167_6935 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_6935.tcenv);
                                       delta_level =
                                         (uu___167_6935.delta_level);
                                       primitive_steps =
                                         (uu___167_6935.primitive_steps)
                                     } in
                                   let uu____6936 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6936)
                          | uu____6937::tl1 ->
                              (log cfg
                                 (fun uu____6947  ->
                                    let uu____6948 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6948);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_6972 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_6972.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6985  ->
                          let uu____6986 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6986);
                     norm cfg env stack2 t1)
                | (Debug uu____6987)::uu____6988 ->
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
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____7021
                                   (fun _0_32  -> Some _0_32)
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
                               let uu___169_7084 = cfg in
                               let uu____7085 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7084.steps);
                                 tcenv = (uu___169_7084.tcenv);
                                 delta_level = (uu___169_7084.delta_level);
                                 primitive_steps = uu____7085
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7095)::uu____7096 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7100 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7100
                    else
                      (let uu____7102 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7102 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7131 =
                                   let uu____7137 =
                                     let uu____7138 =
                                       let uu____7139 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7139 in
                                     FStar_All.pipe_right uu____7138
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7137
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7131
                                   (fun _0_34  -> Some _0_34)
                             | uu____7164 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7178  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7183  ->
                                 let uu____7184 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7184);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7194 = cfg in
                               let uu____7195 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7194.steps);
                                 tcenv = (uu___169_7194.tcenv);
                                 delta_level = (uu___169_7194.delta_level);
                                 primitive_steps = uu____7195
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7205)::uu____7206 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7212 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7212
                    else
                      (let uu____7214 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7214 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7243 =
                                   let uu____7249 =
                                     let uu____7250 =
                                       let uu____7251 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7251 in
                                     FStar_All.pipe_right uu____7250
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7249
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7243
                                   (fun _0_36  -> Some _0_36)
                             | uu____7276 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7290  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7295  ->
                                 let uu____7296 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7296);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7306 = cfg in
                               let uu____7307 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7306.steps);
                                 tcenv = (uu___169_7306.tcenv);
                                 delta_level = (uu___169_7306.delta_level);
                                 primitive_steps = uu____7307
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7317)::uu____7318 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7323 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7323
                    else
                      (let uu____7325 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7325 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7354 =
                                   let uu____7360 =
                                     let uu____7361 =
                                       let uu____7362 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7362 in
                                     FStar_All.pipe_right uu____7361
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7360
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7354
                                   (fun _0_38  -> Some _0_38)
                             | uu____7387 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7401  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7406  ->
                                 let uu____7407 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7407);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7417 = cfg in
                               let uu____7418 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7417.steps);
                                 tcenv = (uu___169_7417.tcenv);
                                 delta_level = (uu___169_7417.delta_level);
                                 primitive_steps = uu____7418
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7428)::uu____7429 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7439 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7439
                    else
                      (let uu____7441 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7441 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7470 =
                                   let uu____7476 =
                                     let uu____7477 =
                                       let uu____7478 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7478 in
                                     FStar_All.pipe_right uu____7477
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7476
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7470
                                   (fun _0_40  -> Some _0_40)
                             | uu____7503 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7517  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7522  ->
                                 let uu____7523 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7523);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7533 = cfg in
                               let uu____7534 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7533.steps);
                                 tcenv = (uu___169_7533.tcenv);
                                 delta_level = (uu___169_7533.delta_level);
                                 primitive_steps = uu____7534
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7544 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7544
                    else
                      (let uu____7546 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7546 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7575 =
                                   let uu____7581 =
                                     let uu____7582 =
                                       let uu____7583 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7583 in
                                     FStar_All.pipe_right uu____7582
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7581
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7575
                                   (fun _0_42  -> Some _0_42)
                             | uu____7608 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7622  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7627  ->
                                 let uu____7628 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7628);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7638 = cfg in
                               let uu____7639 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7638.steps);
                                 tcenv = (uu___169_7638.tcenv);
                                 delta_level = (uu___169_7638.delta_level);
                                 primitive_steps = uu____7639
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
                      (fun uu____7671  ->
                         fun stack2  ->
                           match uu____7671 with
                           | (a,aq) ->
                               let uu____7679 =
                                 let uu____7680 =
                                   let uu____7684 =
                                     let uu____7685 =
                                       let uu____7695 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7695, false) in
                                     Clos uu____7685 in
                                   (uu____7684, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7680 in
                               uu____7679 :: stack2) args) in
               (log cfg
                  (fun uu____7717  ->
                     let uu____7718 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7718);
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
                             ((let uu___170_7739 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7739.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7739.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7740 ->
                      let uu____7743 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7743)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7746 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7746 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7762 =
                          let uu____7763 =
                            let uu____7768 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7769 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7769.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7769.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7768) in
                          FStar_Syntax_Syntax.Tm_refine uu____7763 in
                        mk uu____7762 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7782 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7782
               else
                 (let uu____7784 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7784 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7790 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7796  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7790 c1 in
                      let t2 =
                        let uu____7803 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7803 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7846)::uu____7847 -> norm cfg env stack1 t11
                | (Arg uu____7852)::uu____7853 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7858;
                       FStar_Syntax_Syntax.pos = uu____7859;
                       FStar_Syntax_Syntax.vars = uu____7860;_},uu____7861,uu____7862))::uu____7863
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7869)::uu____7870 ->
                    norm cfg env stack1 t11
                | uu____7875 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7878  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7891 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7891
                        | FStar_Util.Inr c ->
                            let uu____7899 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7899 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7904 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7904)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7955,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7956;
                              FStar_Syntax_Syntax.lbunivs = uu____7957;
                              FStar_Syntax_Syntax.lbtyp = uu____7958;
                              FStar_Syntax_Syntax.lbeff = uu____7959;
                              FStar_Syntax_Syntax.lbdef = uu____7960;_}::uu____7961),uu____7962)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7988 =
                 (let uu____7989 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7989) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7990 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7990))) in
               if uu____7988
               then
                 let env1 =
                   let uu____7993 =
                     let uu____7994 =
                       let uu____8004 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8004,
                         false) in
                     Clos uu____7994 in
                   uu____7993 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8028 =
                    let uu____8031 =
                      let uu____8032 =
                        let uu____8033 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8033
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8032] in
                    FStar_Syntax_Subst.open_term uu____8031 body in
                  match uu____8028 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8039 = lb in
                        let uu____8040 =
                          let uu____8043 =
                            let uu____8044 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8044
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8043
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____8053 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8056 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8040;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8039.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8053;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8039.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8056
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8066  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8082 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8082
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8095 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8117  ->
                        match uu____8117 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8156 =
                                let uu___173_8157 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8157.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8157.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8156 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8095 with
                | (rec_env,memos,uu____8217) ->
                    let uu____8232 =
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
                             let uu____8274 =
                               let uu____8275 =
                                 let uu____8285 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8285, false) in
                               Clos uu____8275 in
                             uu____8274 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8323;
                             FStar_Syntax_Syntax.pos = uu____8324;
                             FStar_Syntax_Syntax.vars = uu____8325;_},uu____8326,uu____8327))::uu____8328
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8334 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8341 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8341
                        then
                          let uu___174_8342 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8342.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8342.primitive_steps)
                          }
                        else
                          (let uu___175_8344 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8344.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8344.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8346 =
                         let uu____8347 = FStar_Syntax_Subst.compress head1 in
                         uu____8347.FStar_Syntax_Syntax.n in
                       match uu____8346 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8361 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8361 with
                            | (uu____8362,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8366 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8373 =
                                         let uu____8374 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8374.FStar_Syntax_Syntax.n in
                                       match uu____8373 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8379,uu____8380))
                                           ->
                                           let uu____8389 =
                                             let uu____8390 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8390.FStar_Syntax_Syntax.n in
                                           (match uu____8389 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8395,msrc,uu____8397))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8406 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8406
                                            | uu____8407 -> None)
                                       | uu____8408 -> None in
                                     let uu____8409 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8409 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8413 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8413.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8413.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8413.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8414 =
                                            FStar_List.tl stack1 in
                                          let uu____8415 =
                                            let uu____8416 =
                                              let uu____8419 =
                                                let uu____8420 =
                                                  let uu____8428 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8428) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8420 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8419 in
                                            uu____8416 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8414 uu____8415
                                      | None  ->
                                          let uu____8445 =
                                            let uu____8446 = is_return body in
                                            match uu____8446 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8449;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8450;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8451;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8456 -> false in
                                          if uu____8445
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
                                               let uu____8476 =
                                                 let uu____8479 =
                                                   let uu____8480 =
                                                     let uu____8495 =
                                                       let uu____8497 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8497] in
                                                     (uu____8495, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8480 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8479 in
                                               uu____8476 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8530 =
                                                 let uu____8531 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8531.FStar_Syntax_Syntax.n in
                                               match uu____8530 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8537::uu____8538::[])
                                                   ->
                                                   let uu____8544 =
                                                     let uu____8547 =
                                                       let uu____8548 =
                                                         let uu____8553 =
                                                           let uu____8555 =
                                                             let uu____8556 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8556 in
                                                           let uu____8557 =
                                                             let uu____8559 =
                                                               let uu____8560
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8560 in
                                                             [uu____8559] in
                                                           uu____8555 ::
                                                             uu____8557 in
                                                         (bind1, uu____8553) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8548 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8547 in
                                                   uu____8544 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8572 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8578 =
                                                 let uu____8581 =
                                                   let uu____8582 =
                                                     let uu____8592 =
                                                       let uu____8594 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8595 =
                                                         let uu____8597 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8598 =
                                                           let uu____8600 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8601 =
                                                             let uu____8603 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8604 =
                                                               let uu____8606
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8607
                                                                 =
                                                                 let uu____8609
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8609] in
                                                               uu____8606 ::
                                                                 uu____8607 in
                                                             uu____8603 ::
                                                               uu____8604 in
                                                           uu____8600 ::
                                                             uu____8601 in
                                                         uu____8597 ::
                                                           uu____8598 in
                                                       uu____8594 ::
                                                         uu____8595 in
                                                     (bind_inst, uu____8592) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8582 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8581 in
                                               uu____8578 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8621 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8621 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8639 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8639 with
                            | (uu____8640,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8663 =
                                        let uu____8664 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8664.FStar_Syntax_Syntax.n in
                                      match uu____8663 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8670) -> t4
                                      | uu____8675 -> head2 in
                                    let uu____8676 =
                                      let uu____8677 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8677.FStar_Syntax_Syntax.n in
                                    match uu____8676 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8682 -> None in
                                  let uu____8683 = maybe_extract_fv head2 in
                                  match uu____8683 with
                                  | Some x when
                                      let uu____8689 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8689
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8693 =
                                          maybe_extract_fv head3 in
                                        match uu____8693 with
                                        | Some uu____8696 -> Some true
                                        | uu____8697 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8700 -> (head2, None) in
                                ((let is_arg_impure uu____8711 =
                                    match uu____8711 with
                                    | (e,q) ->
                                        let uu____8716 =
                                          let uu____8717 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8717.FStar_Syntax_Syntax.n in
                                        (match uu____8716 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8732 -> false) in
                                  let uu____8733 =
                                    let uu____8734 =
                                      let uu____8738 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8738 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8734 in
                                  if uu____8733
                                  then
                                    let uu____8741 =
                                      let uu____8742 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8742 in
                                    failwith uu____8741
                                  else ());
                                 (let uu____8744 =
                                    maybe_unfold_action head_app in
                                  match uu____8744 with
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
                                      let uu____8779 = FStar_List.tl stack1 in
                                      norm cfg env uu____8779 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8793 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8793 in
                           let uu____8794 = FStar_List.tl stack1 in
                           norm cfg env uu____8794 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8877  ->
                                     match uu____8877 with
                                     | (pat,wopt,tm) ->
                                         let uu____8915 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8915))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8941 = FStar_List.tl stack1 in
                           norm cfg env uu____8941 tm
                       | uu____8942 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8951;
                             FStar_Syntax_Syntax.pos = uu____8952;
                             FStar_Syntax_Syntax.vars = uu____8953;_},uu____8954,uu____8955))::uu____8956
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8962 -> false in
                    if should_reify
                    then
                      let uu____8963 = FStar_List.tl stack1 in
                      let uu____8964 =
                        let uu____8965 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8965 in
                      norm cfg env uu____8963 uu____8964
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8968 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8968
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_8974 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_8974.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_8974.primitive_steps)
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
                | uu____8976 ->
                    (match stack1 with
                     | uu____8977::uu____8978 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8982)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8997 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9007 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9007
                           | uu____9014 -> m in
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
              let uu____9026 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9026 with
              | (uu____9027,return_repr) ->
                  let return_inst =
                    let uu____9034 =
                      let uu____9035 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9035.FStar_Syntax_Syntax.n in
                    match uu____9034 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9041::[])
                        ->
                        let uu____9047 =
                          let uu____9050 =
                            let uu____9051 =
                              let uu____9056 =
                                let uu____9058 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9058] in
                              (return_tm, uu____9056) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9051 in
                          FStar_Syntax_Syntax.mk uu____9050 in
                        uu____9047 None e.FStar_Syntax_Syntax.pos
                    | uu____9070 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9073 =
                    let uu____9076 =
                      let uu____9077 =
                        let uu____9087 =
                          let uu____9089 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9090 =
                            let uu____9092 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9092] in
                          uu____9089 :: uu____9090 in
                        (return_inst, uu____9087) in
                      FStar_Syntax_Syntax.Tm_app uu____9077 in
                    FStar_Syntax_Syntax.mk uu____9076 in
                  uu____9073 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9105 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9105 with
               | None  ->
                   let uu____9107 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9107
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9108;
                     FStar_TypeChecker_Env.mtarget = uu____9109;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9110;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9121;
                     FStar_TypeChecker_Env.mtarget = uu____9122;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9123;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9141 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9141)
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
                (fun uu____9171  ->
                   match uu____9171 with
                   | (a,imp) ->
                       let uu____9178 = norm cfg env [] a in
                       (uu____9178, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9193 = comp1 in
            let uu____9196 =
              let uu____9197 =
                let uu____9203 = norm cfg env [] t in
                let uu____9204 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9203, uu____9204) in
              FStar_Syntax_Syntax.Total uu____9197 in
            {
              FStar_Syntax_Syntax.n = uu____9196;
              FStar_Syntax_Syntax.tk = (uu___178_9193.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9193.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9193.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9219 = comp1 in
            let uu____9222 =
              let uu____9223 =
                let uu____9229 = norm cfg env [] t in
                let uu____9230 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9229, uu____9230) in
              FStar_Syntax_Syntax.GTotal uu____9223 in
            {
              FStar_Syntax_Syntax.n = uu____9222;
              FStar_Syntax_Syntax.tk = (uu___179_9219.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9219.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9219.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9261  ->
                      match uu____9261 with
                      | (a,i) ->
                          let uu____9268 = norm cfg env [] a in
                          (uu____9268, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9273  ->
                      match uu___143_9273 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9277 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9277
                      | f -> f)) in
            let uu___180_9281 = comp1 in
            let uu____9284 =
              let uu____9285 =
                let uu___181_9286 = ct in
                let uu____9287 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9288 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9291 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9287;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9286.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9288;
                  FStar_Syntax_Syntax.effect_args = uu____9291;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9285 in
            {
              FStar_Syntax_Syntax.n = uu____9284;
              FStar_Syntax_Syntax.tk = (uu___180_9281.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9281.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9281.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9308 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9308.tcenv);
               delta_level = (uu___182_9308.delta_level);
               primitive_steps = (uu___182_9308.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9313 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9313 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9316 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9330 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9330.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9330.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9330.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9340 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9340
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9345 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9345.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9345.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9345.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9345.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9347 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9347.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9347.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9347.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9347.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9348 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9348.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9348.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9348.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9354 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9357  ->
        match uu____9357 with
        | (x,imp) ->
            let uu____9360 =
              let uu___187_9361 = x in
              let uu____9362 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9361.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9361.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9362
              } in
            (uu____9360, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9368 =
          FStar_List.fold_left
            (fun uu____9375  ->
               fun b  ->
                 match uu____9375 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9368 with | (nbs,uu____9392) -> FStar_List.rev nbs
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
            let uu____9409 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9409
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9414 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9414
               then
                 let uu____9418 =
                   let uu____9421 =
                     let uu____9422 =
                       let uu____9425 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9425 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9422 in
                   FStar_Util.Inl uu____9421 in
                 Some uu____9418
               else
                 (let uu____9429 =
                    let uu____9432 =
                      let uu____9433 =
                        let uu____9436 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9436 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9433 in
                    FStar_Util.Inl uu____9432 in
                  Some uu____9429))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9449 -> lopt
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
              ((let uu____9461 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9461
                then
                  let uu____9462 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9463 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9462
                    uu____9463
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9474 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9474.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9494  ->
                    let uu____9495 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9495);
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
              let uu____9532 =
                let uu___189_9533 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9533.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9533.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9533.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9532
          | (Arg (Univ uu____9538,uu____9539,uu____9540))::uu____9541 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9543,uu____9544))::uu____9545 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9557),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9573  ->
                    let uu____9574 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9574);
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
                 (let uu____9585 = FStar_ST.read m in
                  match uu____9585 with
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
                  | Some (uu____9611,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9633 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9633
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9640  ->
                    let uu____9641 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9641);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9646 =
                  log cfg
                    (fun uu____9648  ->
                       let uu____9649 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9650 =
                         let uu____9651 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9658  ->
                                   match uu____9658 with
                                   | (p,uu____9664,uu____9665) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9651
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9649 uu____9650);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9675  ->
                               match uu___144_9675 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9676 -> false)) in
                     let steps' =
                       let uu____9679 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9679
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9682 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9682.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9682.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9716 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9732 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9766  ->
                                   fun uu____9767  ->
                                     match (uu____9766, uu____9767) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9832 = norm_pat env3 p1 in
                                         (match uu____9832 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9732 with
                          | (pats1,env3) ->
                              ((let uu___191_9898 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_9898.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_9898.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_9912 = x in
                           let uu____9913 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_9912.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_9912.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9913
                           } in
                         ((let uu___193_9919 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_9919.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_9919.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_9924 = x in
                           let uu____9925 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_9924.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_9924.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9925
                           } in
                         ((let uu___195_9931 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_9931.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_9931.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_9941 = x in
                           let uu____9942 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_9941.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_9941.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9942
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_9949 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_9949.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_9949.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9953 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9956 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9956 with
                                 | (p,wopt,e) ->
                                     let uu____9974 = norm_pat env1 p in
                                     (match uu____9974 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9998 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9998 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10003 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10003) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10013) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10018 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10019;
                        FStar_Syntax_Syntax.fv_delta = uu____10020;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10024;
                        FStar_Syntax_Syntax.fv_delta = uu____10025;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10026);_}
                      -> true
                  | uu____10033 -> false in
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
                  let uu____10132 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10132 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10164 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10166 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10168 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10180 ->
                                let uu____10181 =
                                  let uu____10182 = is_cons head1 in
                                  Prims.op_Negation uu____10182 in
                                FStar_Util.Inr uu____10181)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10196 =
                             let uu____10197 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10197.FStar_Syntax_Syntax.n in
                           (match uu____10196 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10204 ->
                                let uu____10205 =
                                  let uu____10206 = is_cons head1 in
                                  Prims.op_Negation uu____10206 in
                                FStar_Util.Inr uu____10205))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10240)::rest_a,(p1,uu____10243)::rest_p) ->
                      let uu____10271 = matches_pat t1 p1 in
                      (match uu____10271 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10285 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10356 = matches_pat scrutinee1 p1 in
                      (match uu____10356 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10366  ->
                                 let uu____10367 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10368 =
                                   let uu____10369 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10369
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10367 uu____10368);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10378 =
                                        let uu____10379 =
                                          let uu____10389 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10389, false) in
                                        Clos uu____10379 in
                                      uu____10378 :: env2) env1 s in
                             let uu____10412 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10412))) in
                let uu____10413 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10413
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10427  ->
                match uu___145_10427 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10430 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10434 -> d in
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
            let uu___198_10454 = config s e in
            {
              steps = (uu___198_10454.steps);
              tcenv = (uu___198_10454.tcenv);
              delta_level = (uu___198_10454.delta_level);
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
      fun t  -> let uu____10473 = config s e in norm_comp uu____10473 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10480 = config [] env in norm_universe uu____10480 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10487 = config [] env in ghost_to_pure_aux uu____10487 [] c
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
        let uu____10499 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10499 in
      let uu____10500 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10500
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10502 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10502.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10502.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10503  ->
                    let uu____10504 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10504))
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
            ((let uu____10517 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10517);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10526 = config [AllowUnboundUniverses] env in
          norm_comp uu____10526 [] c
        with
        | e ->
            ((let uu____10530 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10530);
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
                   let uu____10567 =
                     let uu____10568 =
                       let uu____10573 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10573) in
                     FStar_Syntax_Syntax.Tm_refine uu____10568 in
                   mk uu____10567 t01.FStar_Syntax_Syntax.pos
               | uu____10578 -> t2)
          | uu____10579 -> t2 in
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
        let uu____10601 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10601 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10617 ->
                 let uu____10621 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10621 with
                  | (actuals,uu____10632,uu____10633) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10655 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10655 with
                         | (binders,args) ->
                             let uu____10665 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10668 =
                               let uu____10675 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10675
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10665
                               uu____10668)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10711 =
        let uu____10715 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10715, (t.FStar_Syntax_Syntax.n)) in
      match uu____10711 with
      | (Some sort,uu____10722) ->
          let uu____10724 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10724
      | (uu____10725,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10729 ->
          let uu____10733 = FStar_Syntax_Util.head_and_args t in
          (match uu____10733 with
           | (head1,args) ->
               let uu____10759 =
                 let uu____10760 = FStar_Syntax_Subst.compress head1 in
                 uu____10760.FStar_Syntax_Syntax.n in
               (match uu____10759 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10763,thead) ->
                    let uu____10777 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10777 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10808 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_10812 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_10812.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_10812.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_10812.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_10812.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_10812.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_10812.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_10812.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_10812.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_10812.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_10812.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_10812.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_10812.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_10812.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_10812.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_10812.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_10812.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_10812.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_10812.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_10812.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_10812.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_10812.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_10812.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____10808 with
                            | (uu____10813,ty,uu____10815) ->
                                eta_expand_with_type env t ty))
                | uu____10816 ->
                    let uu____10817 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_10821 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_10821.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_10821.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_10821.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_10821.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_10821.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_10821.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_10821.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_10821.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_10821.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_10821.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_10821.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_10821.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_10821.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_10821.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_10821.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_10821.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_10821.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_10821.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_10821.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_10821.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_10821.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_10821.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____10817 with
                     | (uu____10822,ty,uu____10824) ->
                         eta_expand_with_type env t ty)))