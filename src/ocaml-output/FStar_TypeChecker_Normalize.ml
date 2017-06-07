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
                     | (uu____4826,(p,uu____4828))::(uu____4829,(q,uu____4831))::[]
                         ->
                         let uu____4873 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4873
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4875 -> tm1
                   else
                     (let uu____4885 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4885
                      then
                        let uu____4886 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4886 with
                        | (Some (true ),uu____4919)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4943)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4967 -> tm1
                      else
                        (let uu____4977 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4977
                         then
                           match args with
                           | (t,uu____4979)::[] ->
                               let uu____4992 =
                                 let uu____4993 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4993.FStar_Syntax_Syntax.n in
                               (match uu____4992 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4996::[],body,uu____4998) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5024 -> tm1)
                                | uu____5026 -> tm1)
                           | (uu____5027,Some (FStar_Syntax_Syntax.Implicit
                              uu____5028))::(t,uu____5030)::[] ->
                               let uu____5057 =
                                 let uu____5058 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5058.FStar_Syntax_Syntax.n in
                               (match uu____5057 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5061::[],body,uu____5063) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5089 -> tm1)
                                | uu____5091 -> tm1)
                           | uu____5092 -> tm1
                         else
                           (let uu____5099 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5099
                            then
                              match args with
                              | (t,uu____5101)::[] ->
                                  let uu____5114 =
                                    let uu____5115 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5115.FStar_Syntax_Syntax.n in
                                  (match uu____5114 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5118::[],body,uu____5120) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5146 -> tm1)
                                   | uu____5148 -> tm1)
                              | (uu____5149,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5150))::
                                  (t,uu____5152)::[] ->
                                  let uu____5179 =
                                    let uu____5180 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5180.FStar_Syntax_Syntax.n in
                                  (match uu____5179 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5183::[],body,uu____5185) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5211 -> tm1)
                                   | uu____5213 -> tm1)
                              | uu____5214 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5222;
                FStar_Syntax_Syntax.pos = uu____5223;
                FStar_Syntax_Syntax.vars = uu____5224;_},args)
             ->
             let uu____5240 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5240
             then
               let uu____5241 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5241 with
                | (Some (true ),uu____5274)::(uu____5275,(arg,uu____5277))::[]
                    -> arg
                | (uu____5318,(arg,uu____5320))::(Some (true ),uu____5321)::[]
                    -> arg
                | (Some (false ),uu____5362)::uu____5363::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5401::(Some (false ),uu____5402)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5440 -> tm1)
             else
               (let uu____5450 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5450
                then
                  let uu____5451 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5451 with
                  | (Some (true ),uu____5484)::uu____5485::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5523::(Some (true ),uu____5524)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5562)::(uu____5563,(arg,uu____5565))::[]
                      -> arg
                  | (uu____5606,(arg,uu____5608))::(Some (false ),uu____5609)::[]
                      -> arg
                  | uu____5650 -> tm1
                else
                  (let uu____5660 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5660
                   then
                     let uu____5661 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5661 with
                     | uu____5694::(Some (true ),uu____5695)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5733)::uu____5734::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5772)::(uu____5773,(arg,uu____5775))::[]
                         -> arg
                     | (uu____5816,(p,uu____5818))::(uu____5819,(q,uu____5821))::[]
                         ->
                         let uu____5863 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5863
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5865 -> tm1
                   else
                     (let uu____5875 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5875
                      then
                        let uu____5876 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5876 with
                        | (Some (true ),uu____5909)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5933)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5957 -> tm1
                      else
                        (let uu____5967 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5967
                         then
                           match args with
                           | (t,uu____5969)::[] ->
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
                                     | uu____6014 -> tm1)
                                | uu____6016 -> tm1)
                           | (uu____6017,Some (FStar_Syntax_Syntax.Implicit
                              uu____6018))::(t,uu____6020)::[] ->
                               let uu____6047 =
                                 let uu____6048 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6048.FStar_Syntax_Syntax.n in
                               (match uu____6047 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6051::[],body,uu____6053) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6079 -> tm1)
                                | uu____6081 -> tm1)
                           | uu____6082 -> tm1
                         else
                           (let uu____6089 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6089
                            then
                              match args with
                              | (t,uu____6091)::[] ->
                                  let uu____6104 =
                                    let uu____6105 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6105.FStar_Syntax_Syntax.n in
                                  (match uu____6104 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6108::[],body,uu____6110) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6136 -> tm1)
                                   | uu____6138 -> tm1)
                              | (uu____6139,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6140))::
                                  (t,uu____6142)::[] ->
                                  let uu____6169 =
                                    let uu____6170 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6170.FStar_Syntax_Syntax.n in
                                  (match uu____6169 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6173::[],body,uu____6175) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6201 -> tm1)
                                   | uu____6203 -> tm1)
                              | uu____6204 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6211 -> tm1)
let is_norm_request hd1 args =
  let uu____6226 =
    let uu____6230 =
      let uu____6231 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6231.FStar_Syntax_Syntax.n in
    (uu____6230, args) in
  match uu____6226 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6236::uu____6237::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6240::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6242 -> false
let get_norm_request args =
  match args with
  | uu____6261::(tm,uu____6263)::[] -> tm
  | (tm,uu____6273)::[] -> tm
  | uu____6278 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6285  ->
    match uu___140_6285 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6287;
           FStar_Syntax_Syntax.pos = uu____6288;
           FStar_Syntax_Syntax.vars = uu____6289;_},uu____6290,uu____6291))::uu____6292
        -> true
    | uu____6298 -> false
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
            (fun uu____6413  ->
               let uu____6414 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6415 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6416 =
                 let uu____6417 =
                   let uu____6419 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6419 in
                 stack_to_string uu____6417 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6414
                 uu____6415 uu____6416);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6431 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6452 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6461 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6462 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6463;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6464;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6469;
                 FStar_Syntax_Syntax.fv_delta = uu____6470;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6474;
                 FStar_Syntax_Syntax.fv_delta = uu____6475;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6476);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6509 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6509.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6509.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6509.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6535 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6535) && (is_norm_request hd1 args))
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
                 let uu___166_6548 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6548.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6548.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6553;
                  FStar_Syntax_Syntax.pos = uu____6554;
                  FStar_Syntax_Syntax.vars = uu____6555;_},a1::a2::rest)
               ->
               let uu____6589 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6589 with
                | (hd1,uu____6600) ->
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
                    (FStar_Const.Const_reflect uu____6655);
                  FStar_Syntax_Syntax.tk = uu____6656;
                  FStar_Syntax_Syntax.pos = uu____6657;
                  FStar_Syntax_Syntax.vars = uu____6658;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6681 = FStar_List.tl stack1 in
               norm cfg env uu____6681 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6684;
                  FStar_Syntax_Syntax.pos = uu____6685;
                  FStar_Syntax_Syntax.vars = uu____6686;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6709 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6709 with
                | (reify_head,uu____6720) ->
                    let a1 =
                      let uu____6736 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6736 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6739);
                            FStar_Syntax_Syntax.tk = uu____6740;
                            FStar_Syntax_Syntax.pos = uu____6741;
                            FStar_Syntax_Syntax.vars = uu____6742;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6767 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6775 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6775
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6782 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6782
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6785 =
                      let uu____6789 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6789, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6785 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6798  ->
                         match uu___141_6798 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6801 =
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
                 if uu____6801 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6805 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6805 in
                  let uu____6806 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6806 with
                  | None  ->
                      (log cfg
                         (fun uu____6817  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6823  ->
                            let uu____6824 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6825 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6824 uu____6825);
                       (let t3 =
                          let uu____6827 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6827
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
                          | (UnivArgs (us',uu____6839))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6852 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6853 ->
                              let uu____6854 =
                                let uu____6855 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6855 in
                              failwith uu____6854
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6862 = lookup_bvar env x in
               (match uu____6862 with
                | Univ uu____6863 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6878 = FStar_ST.read r in
                      (match uu____6878 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6897  ->
                                 let uu____6898 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6899 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6898
                                   uu____6899);
                            (let uu____6900 =
                               let uu____6901 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6901.FStar_Syntax_Syntax.n in
                             match uu____6900 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6904 ->
                                 norm cfg env2 stack1 t'
                             | uu____6919 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6952)::uu____6953 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6958)::uu____6959 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6965,uu____6966))::stack_rest ->
                    (match c with
                     | Univ uu____6969 -> norm cfg (c :: env) stack_rest t1
                     | uu____6970 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6973::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6986  ->
                                         let uu____6987 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6987);
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
                                           (fun uu___142_7001  ->
                                              match uu___142_7001 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____7002 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7004  ->
                                         let uu____7005 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7005);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____7016  ->
                                         let uu____7017 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7017);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____7018 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7025 ->
                                   let cfg1 =
                                     let uu___167_7033 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_7033.tcenv);
                                       delta_level =
                                         (uu___167_7033.delta_level);
                                       primitive_steps =
                                         (uu___167_7033.primitive_steps)
                                     } in
                                   let uu____7034 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7034)
                          | uu____7035::tl1 ->
                              (log cfg
                                 (fun uu____7045  ->
                                    let uu____7046 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7046);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_7070 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_7070.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7083  ->
                          let uu____7084 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7084);
                     norm cfg env stack2 t1)
                | (Debug uu____7085)::uu____7086 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7088 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7088
                    else
                      (let uu____7090 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7090 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7119 =
                                   let uu____7125 =
                                     let uu____7126 =
                                       let uu____7127 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7127 in
                                     FStar_All.pipe_right uu____7126
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7125
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____7119
                                   (fun _0_32  -> Some _0_32)
                             | uu____7152 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7166  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7171  ->
                                 let uu____7172 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7172);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7182 = cfg in
                               let uu____7183 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7182.steps);
                                 tcenv = (uu___169_7182.tcenv);
                                 delta_level = (uu___169_7182.delta_level);
                                 primitive_steps = uu____7183
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7193)::uu____7194 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7198 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7198
                    else
                      (let uu____7200 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7200 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7229 =
                                   let uu____7235 =
                                     let uu____7236 =
                                       let uu____7237 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7237 in
                                     FStar_All.pipe_right uu____7236
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7235
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7229
                                   (fun _0_34  -> Some _0_34)
                             | uu____7262 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7276  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7281  ->
                                 let uu____7282 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7282);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7292 = cfg in
                               let uu____7293 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7292.steps);
                                 tcenv = (uu___169_7292.tcenv);
                                 delta_level = (uu___169_7292.delta_level);
                                 primitive_steps = uu____7293
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7303)::uu____7304 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7310 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7310
                    else
                      (let uu____7312 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7312 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7341 =
                                   let uu____7347 =
                                     let uu____7348 =
                                       let uu____7349 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7349 in
                                     FStar_All.pipe_right uu____7348
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7347
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7341
                                   (fun _0_36  -> Some _0_36)
                             | uu____7374 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7388  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7393  ->
                                 let uu____7394 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7394);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7404 = cfg in
                               let uu____7405 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7404.steps);
                                 tcenv = (uu___169_7404.tcenv);
                                 delta_level = (uu___169_7404.delta_level);
                                 primitive_steps = uu____7405
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7415)::uu____7416 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7421 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7421
                    else
                      (let uu____7423 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7423 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7452 =
                                   let uu____7458 =
                                     let uu____7459 =
                                       let uu____7460 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7460 in
                                     FStar_All.pipe_right uu____7459
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7458
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7452
                                   (fun _0_38  -> Some _0_38)
                             | uu____7485 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7499  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7504  ->
                                 let uu____7505 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7505);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7515 = cfg in
                               let uu____7516 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7515.steps);
                                 tcenv = (uu___169_7515.tcenv);
                                 delta_level = (uu___169_7515.delta_level);
                                 primitive_steps = uu____7516
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7526)::uu____7527 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7537 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7537
                    else
                      (let uu____7539 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7539 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7568 =
                                   let uu____7574 =
                                     let uu____7575 =
                                       let uu____7576 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7576 in
                                     FStar_All.pipe_right uu____7575
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7574
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7568
                                   (fun _0_40  -> Some _0_40)
                             | uu____7601 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7615  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7620  ->
                                 let uu____7621 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7621);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7631 = cfg in
                               let uu____7632 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7631.steps);
                                 tcenv = (uu___169_7631.tcenv);
                                 delta_level = (uu___169_7631.delta_level);
                                 primitive_steps = uu____7632
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7642 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7642
                    else
                      (let uu____7644 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7644 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7673 =
                                   let uu____7679 =
                                     let uu____7680 =
                                       let uu____7681 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7681 in
                                     FStar_All.pipe_right uu____7680
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7679
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7673
                                   (fun _0_42  -> Some _0_42)
                             | uu____7706 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7720  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7725  ->
                                 let uu____7726 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7726);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7736 = cfg in
                               let uu____7737 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7736.steps);
                                 tcenv = (uu___169_7736.tcenv);
                                 delta_level = (uu___169_7736.delta_level);
                                 primitive_steps = uu____7737
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
                      (fun uu____7769  ->
                         fun stack2  ->
                           match uu____7769 with
                           | (a,aq) ->
                               let uu____7777 =
                                 let uu____7778 =
                                   let uu____7782 =
                                     let uu____7783 =
                                       let uu____7793 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7793, false) in
                                     Clos uu____7783 in
                                   (uu____7782, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7778 in
                               uu____7777 :: stack2) args) in
               (log cfg
                  (fun uu____7815  ->
                     let uu____7816 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7816);
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
                             ((let uu___170_7837 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7837.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7837.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7838 ->
                      let uu____7841 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7841)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7844 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7844 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7860 =
                          let uu____7861 =
                            let uu____7866 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7867 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7867.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7867.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7866) in
                          FStar_Syntax_Syntax.Tm_refine uu____7861 in
                        mk uu____7860 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7880 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7880
               else
                 (let uu____7882 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7882 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7888 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7894  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7888 c1 in
                      let t2 =
                        let uu____7901 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7901 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7944)::uu____7945 -> norm cfg env stack1 t11
                | (Arg uu____7950)::uu____7951 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7956;
                       FStar_Syntax_Syntax.pos = uu____7957;
                       FStar_Syntax_Syntax.vars = uu____7958;_},uu____7959,uu____7960))::uu____7961
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7967)::uu____7968 ->
                    norm cfg env stack1 t11
                | uu____7973 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7976  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7989 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7989
                        | FStar_Util.Inr c ->
                            let uu____7997 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7997 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____8002 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____8002)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____8053,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____8054;
                              FStar_Syntax_Syntax.lbunivs = uu____8055;
                              FStar_Syntax_Syntax.lbtyp = uu____8056;
                              FStar_Syntax_Syntax.lbeff = uu____8057;
                              FStar_Syntax_Syntax.lbdef = uu____8058;_}::uu____8059),uu____8060)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8086 =
                 (let uu____8087 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8087) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8088 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8088))) in
               if uu____8086
               then
                 let env1 =
                   let uu____8091 =
                     let uu____8092 =
                       let uu____8102 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8102,
                         false) in
                     Clos uu____8092 in
                   uu____8091 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8126 =
                    let uu____8129 =
                      let uu____8130 =
                        let uu____8131 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8131
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8130] in
                    FStar_Syntax_Subst.open_term uu____8129 body in
                  match uu____8126 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8137 = lb in
                        let uu____8138 =
                          let uu____8141 =
                            let uu____8142 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8142
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8141
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____8151 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8154 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8138;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8137.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8151;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8137.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8154
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8164  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8180 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8180
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8193 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8215  ->
                        match uu____8215 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8254 =
                                let uu___173_8255 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8255.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8255.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8254 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8193 with
                | (rec_env,memos,uu____8315) ->
                    let uu____8330 =
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
                             let uu____8372 =
                               let uu____8373 =
                                 let uu____8383 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8383, false) in
                               Clos uu____8373 in
                             uu____8372 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8421;
                             FStar_Syntax_Syntax.pos = uu____8422;
                             FStar_Syntax_Syntax.vars = uu____8423;_},uu____8424,uu____8425))::uu____8426
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8432 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8439 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8439
                        then
                          let uu___174_8440 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8440.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8440.primitive_steps)
                          }
                        else
                          (let uu___175_8442 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8442.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8442.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8444 =
                         let uu____8445 = FStar_Syntax_Subst.compress head1 in
                         uu____8445.FStar_Syntax_Syntax.n in
                       match uu____8444 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8459 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8459 with
                            | (uu____8460,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8464 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8471 =
                                         let uu____8472 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8472.FStar_Syntax_Syntax.n in
                                       match uu____8471 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8477,uu____8478))
                                           ->
                                           let uu____8487 =
                                             let uu____8488 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8488.FStar_Syntax_Syntax.n in
                                           (match uu____8487 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8493,msrc,uu____8495))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8504 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8504
                                            | uu____8505 -> None)
                                       | uu____8506 -> None in
                                     let uu____8507 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8507 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8511 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8511.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8511.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8511.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8512 =
                                            FStar_List.tl stack1 in
                                          let uu____8513 =
                                            let uu____8514 =
                                              let uu____8517 =
                                                let uu____8518 =
                                                  let uu____8526 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8526) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8518 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8517 in
                                            uu____8514 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8512 uu____8513
                                      | None  ->
                                          let uu____8543 =
                                            let uu____8544 = is_return body in
                                            match uu____8544 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8547;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8548;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8549;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8554 -> false in
                                          if uu____8543
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
                                               let uu____8574 =
                                                 let uu____8577 =
                                                   let uu____8578 =
                                                     let uu____8593 =
                                                       let uu____8595 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8595] in
                                                     (uu____8593, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8578 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8577 in
                                               uu____8574 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8628 =
                                                 let uu____8629 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8629.FStar_Syntax_Syntax.n in
                                               match uu____8628 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8635::uu____8636::[])
                                                   ->
                                                   let uu____8642 =
                                                     let uu____8645 =
                                                       let uu____8646 =
                                                         let uu____8651 =
                                                           let uu____8653 =
                                                             let uu____8654 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8654 in
                                                           let uu____8655 =
                                                             let uu____8657 =
                                                               let uu____8658
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8658 in
                                                             [uu____8657] in
                                                           uu____8653 ::
                                                             uu____8655 in
                                                         (bind1, uu____8651) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8646 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8645 in
                                                   uu____8642 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8670 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8676 =
                                                 let uu____8679 =
                                                   let uu____8680 =
                                                     let uu____8690 =
                                                       let uu____8692 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8693 =
                                                         let uu____8695 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8696 =
                                                           let uu____8698 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8699 =
                                                             let uu____8701 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8702 =
                                                               let uu____8704
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8705
                                                                 =
                                                                 let uu____8707
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8707] in
                                                               uu____8704 ::
                                                                 uu____8705 in
                                                             uu____8701 ::
                                                               uu____8702 in
                                                           uu____8698 ::
                                                             uu____8699 in
                                                         uu____8695 ::
                                                           uu____8696 in
                                                       uu____8692 ::
                                                         uu____8693 in
                                                     (bind_inst, uu____8690) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8680 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8679 in
                                               uu____8676 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8719 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8719 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8737 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8737 with
                            | (uu____8738,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8761 =
                                        let uu____8762 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8762.FStar_Syntax_Syntax.n in
                                      match uu____8761 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8768) -> t4
                                      | uu____8773 -> head2 in
                                    let uu____8774 =
                                      let uu____8775 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8775.FStar_Syntax_Syntax.n in
                                    match uu____8774 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8780 -> None in
                                  let uu____8781 = maybe_extract_fv head2 in
                                  match uu____8781 with
                                  | Some x when
                                      let uu____8787 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8787
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8791 =
                                          maybe_extract_fv head3 in
                                        match uu____8791 with
                                        | Some uu____8794 -> Some true
                                        | uu____8795 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8798 -> (head2, None) in
                                ((let is_arg_impure uu____8809 =
                                    match uu____8809 with
                                    | (e,q) ->
                                        let uu____8814 =
                                          let uu____8815 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8815.FStar_Syntax_Syntax.n in
                                        (match uu____8814 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8830 -> false) in
                                  let uu____8831 =
                                    let uu____8832 =
                                      let uu____8836 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8836 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8832 in
                                  if uu____8831
                                  then
                                    let uu____8839 =
                                      let uu____8840 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8840 in
                                    failwith uu____8839
                                  else ());
                                 (let uu____8842 =
                                    maybe_unfold_action head_app in
                                  match uu____8842 with
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
                                      let uu____8877 = FStar_List.tl stack1 in
                                      norm cfg env uu____8877 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8891 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8891 in
                           let uu____8892 = FStar_List.tl stack1 in
                           norm cfg env uu____8892 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8975  ->
                                     match uu____8975 with
                                     | (pat,wopt,tm) ->
                                         let uu____9013 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9013))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9039 = FStar_List.tl stack1 in
                           norm cfg env uu____9039 tm
                       | uu____9040 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9049;
                             FStar_Syntax_Syntax.pos = uu____9050;
                             FStar_Syntax_Syntax.vars = uu____9051;_},uu____9052,uu____9053))::uu____9054
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9060 -> false in
                    if should_reify
                    then
                      let uu____9061 = FStar_List.tl stack1 in
                      let uu____9062 =
                        let uu____9063 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9063 in
                      norm cfg env uu____9061 uu____9062
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9066 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9066
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_9072 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_9072.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_9072.primitive_steps)
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
                | uu____9074 ->
                    (match stack1 with
                     | uu____9075::uu____9076 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9080)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____9095 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9105 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9105
                           | uu____9112 -> m in
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
              let uu____9124 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9124 with
              | (uu____9125,return_repr) ->
                  let return_inst =
                    let uu____9132 =
                      let uu____9133 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9133.FStar_Syntax_Syntax.n in
                    match uu____9132 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9139::[])
                        ->
                        let uu____9145 =
                          let uu____9148 =
                            let uu____9149 =
                              let uu____9154 =
                                let uu____9156 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9156] in
                              (return_tm, uu____9154) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9149 in
                          FStar_Syntax_Syntax.mk uu____9148 in
                        uu____9145 None e.FStar_Syntax_Syntax.pos
                    | uu____9168 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9171 =
                    let uu____9174 =
                      let uu____9175 =
                        let uu____9185 =
                          let uu____9187 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9188 =
                            let uu____9190 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9190] in
                          uu____9187 :: uu____9188 in
                        (return_inst, uu____9185) in
                      FStar_Syntax_Syntax.Tm_app uu____9175 in
                    FStar_Syntax_Syntax.mk uu____9174 in
                  uu____9171 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9203 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9203 with
               | None  ->
                   let uu____9205 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9205
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9206;
                     FStar_TypeChecker_Env.mtarget = uu____9207;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9208;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9219;
                     FStar_TypeChecker_Env.mtarget = uu____9220;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9221;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9239 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9239)
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
                (fun uu____9269  ->
                   match uu____9269 with
                   | (a,imp) ->
                       let uu____9276 = norm cfg env [] a in
                       (uu____9276, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9291 = comp1 in
            let uu____9294 =
              let uu____9295 =
                let uu____9301 = norm cfg env [] t in
                let uu____9302 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9301, uu____9302) in
              FStar_Syntax_Syntax.Total uu____9295 in
            {
              FStar_Syntax_Syntax.n = uu____9294;
              FStar_Syntax_Syntax.tk = (uu___178_9291.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9291.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9291.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9317 = comp1 in
            let uu____9320 =
              let uu____9321 =
                let uu____9327 = norm cfg env [] t in
                let uu____9328 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9327, uu____9328) in
              FStar_Syntax_Syntax.GTotal uu____9321 in
            {
              FStar_Syntax_Syntax.n = uu____9320;
              FStar_Syntax_Syntax.tk = (uu___179_9317.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9317.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9317.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9359  ->
                      match uu____9359 with
                      | (a,i) ->
                          let uu____9366 = norm cfg env [] a in
                          (uu____9366, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9371  ->
                      match uu___143_9371 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9375 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9375
                      | f -> f)) in
            let uu___180_9379 = comp1 in
            let uu____9382 =
              let uu____9383 =
                let uu___181_9384 = ct in
                let uu____9385 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9386 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9389 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9385;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9384.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9386;
                  FStar_Syntax_Syntax.effect_args = uu____9389;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9383 in
            {
              FStar_Syntax_Syntax.n = uu____9382;
              FStar_Syntax_Syntax.tk = (uu___180_9379.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9379.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9379.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9406 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9406.tcenv);
               delta_level = (uu___182_9406.delta_level);
               primitive_steps = (uu___182_9406.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9411 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9411 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9414 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9428 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9428.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9428.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9428.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9438 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9438
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9443 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9443.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9443.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9443.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9443.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9445 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9445.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9445.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9445.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9445.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9446 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9446.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9446.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9446.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9452 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9455  ->
        match uu____9455 with
        | (x,imp) ->
            let uu____9458 =
              let uu___187_9459 = x in
              let uu____9460 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9459.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9459.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9460
              } in
            (uu____9458, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9466 =
          FStar_List.fold_left
            (fun uu____9473  ->
               fun b  ->
                 match uu____9473 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9466 with | (nbs,uu____9490) -> FStar_List.rev nbs
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
            let uu____9507 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9507
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9512 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9512
               then
                 let uu____9516 =
                   let uu____9519 =
                     let uu____9520 =
                       let uu____9523 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9523 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9520 in
                   FStar_Util.Inl uu____9519 in
                 Some uu____9516
               else
                 (let uu____9527 =
                    let uu____9530 =
                      let uu____9531 =
                        let uu____9534 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9534 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9531 in
                    FStar_Util.Inl uu____9530 in
                  Some uu____9527))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9547 -> lopt
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
              ((let uu____9559 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9559
                then
                  let uu____9560 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9561 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9560
                    uu____9561
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9572 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9572.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9592  ->
                    let uu____9593 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9593);
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
              let uu____9630 =
                let uu___189_9631 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9631.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9631.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9631.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9630
          | (Arg (Univ uu____9636,uu____9637,uu____9638))::uu____9639 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9641,uu____9642))::uu____9643 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9655),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9671  ->
                    let uu____9672 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9672);
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
                 (let uu____9683 = FStar_ST.read m in
                  match uu____9683 with
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
                  | Some (uu____9709,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9731 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9731
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9738  ->
                    let uu____9739 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9739);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9744 =
                  log cfg
                    (fun uu____9746  ->
                       let uu____9747 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9748 =
                         let uu____9749 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9756  ->
                                   match uu____9756 with
                                   | (p,uu____9762,uu____9763) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9749
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9747 uu____9748);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9773  ->
                               match uu___144_9773 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9774 -> false)) in
                     let steps' =
                       let uu____9777 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9777
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9780 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9780.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9780.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9814 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9830 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9864  ->
                                   fun uu____9865  ->
                                     match (uu____9864, uu____9865) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9930 = norm_pat env3 p1 in
                                         (match uu____9930 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9830 with
                          | (pats1,env3) ->
                              ((let uu___191_9996 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_9996.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_9996.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_10010 = x in
                           let uu____10011 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_10010.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_10010.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10011
                           } in
                         ((let uu___193_10017 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_10017.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_10017.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_10022 = x in
                           let uu____10023 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_10022.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_10022.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10023
                           } in
                         ((let uu___195_10029 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_10029.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_10029.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_10039 = x in
                           let uu____10040 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_10039.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_10039.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10040
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_10047 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_10047.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_10047.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10051 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10054 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10054 with
                                 | (p,wopt,e) ->
                                     let uu____10072 = norm_pat env1 p in
                                     (match uu____10072 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10096 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10096 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10101 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10101) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10111) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10116 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10117;
                        FStar_Syntax_Syntax.fv_delta = uu____10118;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10122;
                        FStar_Syntax_Syntax.fv_delta = uu____10123;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10124);_}
                      -> true
                  | uu____10131 -> false in
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
                  let uu____10230 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10230 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10262 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10264 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10266 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10278 ->
                                let uu____10279 =
                                  let uu____10280 = is_cons head1 in
                                  Prims.op_Negation uu____10280 in
                                FStar_Util.Inr uu____10279)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10294 =
                             let uu____10295 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10295.FStar_Syntax_Syntax.n in
                           (match uu____10294 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10302 ->
                                let uu____10303 =
                                  let uu____10304 = is_cons head1 in
                                  Prims.op_Negation uu____10304 in
                                FStar_Util.Inr uu____10303))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10338)::rest_a,(p1,uu____10341)::rest_p) ->
                      let uu____10369 = matches_pat t1 p1 in
                      (match uu____10369 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10383 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10454 = matches_pat scrutinee1 p1 in
                      (match uu____10454 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10464  ->
                                 let uu____10465 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10466 =
                                   let uu____10467 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10467
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10465 uu____10466);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10476 =
                                        let uu____10477 =
                                          let uu____10487 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10487, false) in
                                        Clos uu____10477 in
                                      uu____10476 :: env2) env1 s in
                             let uu____10510 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10510))) in
                let uu____10511 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10511
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10525  ->
                match uu___145_10525 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10528 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10532 -> d in
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
            let uu___198_10552 = config s e in
            {
              steps = (uu___198_10552.steps);
              tcenv = (uu___198_10552.tcenv);
              delta_level = (uu___198_10552.delta_level);
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
      fun t  -> let uu____10571 = config s e in norm_comp uu____10571 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10578 = config [] env in norm_universe uu____10578 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10585 = config [] env in ghost_to_pure_aux uu____10585 [] c
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
        let uu____10597 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10597 in
      let uu____10598 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10598
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10600 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10600.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10600.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10601  ->
                    let uu____10602 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10602))
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
            ((let uu____10615 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10615);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10624 = config [AllowUnboundUniverses] env in
          norm_comp uu____10624 [] c
        with
        | e ->
            ((let uu____10628 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10628);
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
                   let uu____10665 =
                     let uu____10666 =
                       let uu____10671 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10671) in
                     FStar_Syntax_Syntax.Tm_refine uu____10666 in
                   mk uu____10665 t01.FStar_Syntax_Syntax.pos
               | uu____10676 -> t2)
          | uu____10677 -> t2 in
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
        let uu____10699 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10699 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10715 ->
                 let uu____10719 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10719 with
                  | (actuals,uu____10730,uu____10731) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10753 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10753 with
                         | (binders,args) ->
                             let uu____10763 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10766 =
                               let uu____10773 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10773
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10763
                               uu____10766)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10809 =
        let uu____10813 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10813, (t.FStar_Syntax_Syntax.n)) in
      match uu____10809 with
      | (Some sort,uu____10820) ->
          let uu____10822 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10822
      | (uu____10823,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10827 ->
          let uu____10831 = FStar_Syntax_Util.head_and_args t in
          (match uu____10831 with
           | (head1,args) ->
               let uu____10857 =
                 let uu____10858 = FStar_Syntax_Subst.compress head1 in
                 uu____10858.FStar_Syntax_Syntax.n in
               (match uu____10857 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10861,thead) ->
                    let uu____10875 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10875 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10906 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_10910 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_10910.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_10910.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_10910.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_10910.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_10910.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_10910.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_10910.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_10910.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_10910.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_10910.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_10910.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_10910.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_10910.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_10910.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_10910.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_10910.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_10910.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_10910.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_10910.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_10910.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_10910.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_10910.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____10906 with
                            | (uu____10911,ty,uu____10913) ->
                                eta_expand_with_type env t ty))
                | uu____10914 ->
                    let uu____10915 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_10919 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_10919.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_10919.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_10919.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_10919.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_10919.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_10919.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_10919.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_10919.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_10919.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_10919.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_10919.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_10919.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_10919.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_10919.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_10919.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_10919.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_10919.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_10919.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_10919.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_10919.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_10919.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_10919.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____10915 with
                     | (uu____10920,ty,uu____10922) ->
                         eta_expand_with_type env t ty)))