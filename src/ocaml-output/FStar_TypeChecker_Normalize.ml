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
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____66 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____70 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____74 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____78 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____82 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____86 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____90 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____94 -> false
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
    match projectee with | Clos _0 -> true | uu____169 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____208 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____219 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___135_223  ->
    match uu___135_223 with
    | Clos (uu____224,t,uu____226,uu____227) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____238 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____351 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____375 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____399 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____426 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____455 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____494 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____517 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____539 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____568 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____595 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____607 =
      let uu____608 = FStar_Syntax_Util.un_uinst t in
      uu____608.FStar_Syntax_Syntax.n in
    match uu____607 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_refl_embed_lid
    | uu____612 -> false
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____652 = FStar_ST.read r in
  match uu____652 with
  | Some uu____657 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____666 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____666 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___136_671  ->
    match uu___136_671 with
    | Arg (c,uu____673,uu____674) ->
        let uu____675 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____675
    | MemoLazy uu____676 -> "MemoLazy"
    | Abs (uu____680,bs,uu____682,uu____683,uu____684) ->
        let uu____691 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____691
    | UnivArgs uu____698 -> "UnivArgs"
    | Match uu____702 -> "Match"
    | App (t,uu____707,uu____708) ->
        let uu____709 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____709
    | Meta (m,uu____711) -> "Meta"
    | Let uu____712 -> "Let"
    | Steps (uu____717,uu____718,uu____719) -> "Steps"
    | Debug t ->
        let uu____725 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____725
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____731 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____731 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____745 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____745 then f () else ()
let is_empty uu___137_754 =
  match uu___137_754 with | [] -> true | uu____756 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____774 ->
      let uu____775 =
        let uu____776 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____776 in
      failwith uu____775
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
          let uu____807 =
            FStar_List.fold_left
              (fun uu____816  ->
                 fun u1  ->
                   match uu____816 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____831 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____831 with
                        | (k_u,n1) ->
                            let uu____840 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____840
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____807 with
          | (uu____850,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____866 = FStar_List.nth env x in
                 match uu____866 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____869 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____873 ->
                   let uu____874 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____874
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____878 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____881 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____886 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____886 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____897 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____897 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____902 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____905 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____905 with
                                  | (uu____908,m) -> n1 <= m)) in
                        if uu____902 then rest1 else us1
                    | uu____912 -> us1)
               | uu____915 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____918 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____918 in
        let uu____920 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____920
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____922 = aux u in
           match uu____922 with
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
          (fun uu____1019  ->
             let uu____1020 = FStar_Syntax_Print.tag_of_term t in
             let uu____1021 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1020
               uu____1021);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1022 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1025 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1046 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1047 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1048 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1049 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1059 =
                    let uu____1060 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1060 in
                  mk uu____1059 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1067 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1067
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1069 = lookup_bvar env x in
                  (match uu____1069 with
                   | Univ uu____1070 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1074) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1142 = closures_as_binders_delayed cfg env bs in
                  (match uu____1142 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1162 =
                         let uu____1163 =
                           let uu____1178 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1178) in
                         FStar_Syntax_Syntax.Tm_abs uu____1163 in
                       mk uu____1162 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1208 = closures_as_binders_delayed cfg env bs in
                  (match uu____1208 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1239 =
                    let uu____1246 =
                      let uu____1250 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1250] in
                    closures_as_binders_delayed cfg env uu____1246 in
                  (match uu____1239 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1264 =
                         let uu____1265 =
                           let uu____1270 =
                             let uu____1271 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1271
                               FStar_Pervasives.fst in
                           (uu____1270, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1265 in
                       mk uu____1264 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1339 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1339
                    | FStar_Util.Inr c ->
                        let uu____1353 = close_comp cfg env c in
                        FStar_Util.Inr uu____1353 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1368 =
                    let uu____1369 =
                      let uu____1387 = closure_as_term_delayed cfg env t11 in
                      (uu____1387, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1369 in
                  mk uu____1368 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1425 =
                    let uu____1426 =
                      let uu____1431 = closure_as_term_delayed cfg env t' in
                      let uu____1434 =
                        let uu____1435 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1435 in
                      (uu____1431, uu____1434) in
                    FStar_Syntax_Syntax.Tm_meta uu____1426 in
                  mk uu____1425 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1477 =
                    let uu____1478 =
                      let uu____1483 = closure_as_term_delayed cfg env t' in
                      let uu____1486 =
                        let uu____1487 =
                          let uu____1492 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1492) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1487 in
                      (uu____1483, uu____1486) in
                    FStar_Syntax_Syntax.Tm_meta uu____1478 in
                  mk uu____1477 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1511 =
                    let uu____1512 =
                      let uu____1517 = closure_as_term_delayed cfg env t' in
                      let uu____1520 =
                        let uu____1521 =
                          let uu____1527 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1527) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1521 in
                      (uu____1517, uu____1520) in
                    FStar_Syntax_Syntax.Tm_meta uu____1512 in
                  mk uu____1511 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1540 =
                    let uu____1541 =
                      let uu____1546 = closure_as_term_delayed cfg env t' in
                      (uu____1546, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1541 in
                  mk uu____1540 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1567  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1578 -> body
                    | FStar_Util.Inl uu____1579 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___150_1581 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1581.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1581.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1581.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1588,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1612  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1617 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1617
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1621  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___151_1624 = lb in
                    let uu____1625 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1628 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1624.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1624.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1625;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1624.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1628
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1639  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1694 =
                    match uu____1694 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1740 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1756 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1790  ->
                                        fun uu____1791  ->
                                          match (uu____1790, uu____1791) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1856 =
                                                norm_pat env3 p1 in
                                              (match uu____1856 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1756 with
                               | (pats1,env3) ->
                                   ((let uu___152_1922 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_1922.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_1922.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___153_1936 = x in
                                let uu____1937 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_1936.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_1936.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1937
                                } in
                              ((let uu___154_1943 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_1943.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_1943.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___155_1948 = x in
                                let uu____1949 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_1948.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_1948.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1949
                                } in
                              ((let uu___156_1955 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_1955.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_1955.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___157_1965 = x in
                                let uu____1966 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_1965.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_1965.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1966
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___158_1973 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_1973.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_1973.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1976 = norm_pat env1 pat in
                        (match uu____1976 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2000 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2000 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2005 =
                    let uu____2006 =
                      let uu____2022 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2022) in
                    FStar_Syntax_Syntax.Tm_match uu____2006 in
                  mk uu____2005 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2075 -> closure_as_term cfg env t
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
        | uu____2091 ->
            FStar_List.map
              (fun uu____2101  ->
                 match uu____2101 with
                 | (x,imp) ->
                     let uu____2116 = closure_as_term_delayed cfg env x in
                     (uu____2116, imp)) args
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
        let uu____2128 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2152  ->
                  fun uu____2153  ->
                    match (uu____2152, uu____2153) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___159_2197 = b in
                          let uu____2198 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___159_2197.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___159_2197.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2198
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2128 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2245 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2257 = closure_as_term_delayed cfg env t in
                 let uu____2258 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2257 uu____2258
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2268 = closure_as_term_delayed cfg env t in
                 let uu____2269 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2268 uu____2269
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
                        (fun uu___138_2285  ->
                           match uu___138_2285 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2289 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2289
                           | f -> f)) in
                 let uu____2293 =
                   let uu___160_2294 = c1 in
                   let uu____2295 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2295;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___160_2294.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2293)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___139_2299  ->
            match uu___139_2299 with
            | FStar_Syntax_Syntax.DECREASES uu____2300 -> false
            | uu____2303 -> true))
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
            let uu____2331 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2331
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2348 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2348
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2374 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2398 =
      let uu____2399 =
        let uu____2405 = FStar_Util.string_of_int i in (uu____2405, None) in
      FStar_Const.Const_int uu____2399 in
    const_as_tm uu____2398 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2432 =
    match uu____2432 with
    | (a,uu____2437) ->
        let uu____2439 =
          let uu____2440 = FStar_Syntax_Subst.compress a in
          uu____2440.FStar_Syntax_Syntax.n in
        (match uu____2439 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2450 = FStar_Util.int_of_string i in Some uu____2450
         | uu____2451 -> None) in
  let arg_as_bounded_int uu____2460 =
    match uu____2460 with
    | (a,uu____2467) ->
        let uu____2471 =
          let uu____2472 = FStar_Syntax_Subst.compress a in
          uu____2472.FStar_Syntax_Syntax.n in
        (match uu____2471 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2479;
                FStar_Syntax_Syntax.pos = uu____2480;
                FStar_Syntax_Syntax.vars = uu____2481;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2483;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2484;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2485;_},uu____2486)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2517 =
               let uu____2520 = FStar_Util.int_of_string i in
               (fv1, uu____2520) in
             Some uu____2517
         | uu____2523 -> None) in
  let arg_as_bool uu____2532 =
    match uu____2532 with
    | (a,uu____2537) ->
        let uu____2539 =
          let uu____2540 = FStar_Syntax_Subst.compress a in
          uu____2540.FStar_Syntax_Syntax.n in
        (match uu____2539 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2545 -> None) in
  let arg_as_char uu____2552 =
    match uu____2552 with
    | (a,uu____2557) ->
        let uu____2559 =
          let uu____2560 = FStar_Syntax_Subst.compress a in
          uu____2560.FStar_Syntax_Syntax.n in
        (match uu____2559 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2565 -> None) in
  let arg_as_string uu____2572 =
    match uu____2572 with
    | (a,uu____2577) ->
        let uu____2579 =
          let uu____2580 = FStar_Syntax_Subst.compress a in
          uu____2580.FStar_Syntax_Syntax.n in
        (match uu____2579 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2585)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2588 -> None) in
  let arg_as_list f uu____2609 =
    match uu____2609 with
    | (a,uu____2618) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2637 -> None
          | (Some x)::xs ->
              let uu____2647 = sequence xs in
              (match uu____2647 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2658 = FStar_Syntax_Util.list_elements a in
        (match uu____2658 with
         | None  -> None
         | Some elts ->
             let uu____2668 =
               FStar_List.map
                 (fun x  ->
                    let uu____2673 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2673) elts in
             sequence uu____2668) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2703 = f a in Some uu____2703
    | uu____2704 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2743 = f a0 a1 in Some uu____2743
    | uu____2744 -> None in
  let unary_op as_a f r args =
    let uu____2788 = FStar_List.map as_a args in lift_unary (f r) uu____2788 in
  let binary_op as_a f r args =
    let uu____2838 = FStar_List.map as_a args in lift_binary (f r) uu____2838 in
  let as_primitive_step uu____2855 =
    match uu____2855 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2893 = f x in int_as_const r uu____2893) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2916 = f x y in int_as_const r uu____2916) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2933 = f x in bool_as_const r uu____2933) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2956 = f x y in bool_as_const r uu____2956) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2979 = f x y in string_as_const r uu____2979) in
  let list_of_string' rng s =
    let name l =
      let uu____2993 =
        let uu____2994 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2994 in
      mk uu____2993 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3004 =
      let uu____3006 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3006 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3004 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3060 = arg_as_string a1 in
        (match uu____3060 with
         | Some s1 ->
             let uu____3064 = arg_as_list arg_as_string a2 in
             (match uu____3064 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3072 = string_as_const rng r in Some uu____3072
              | uu____3073 -> None)
         | uu____3076 -> None)
    | uu____3078 -> None in
  let string_of_int1 rng i =
    let uu____3089 = FStar_Util.string_of_int i in
    string_as_const rng uu____3089 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3105 = FStar_Util.string_of_int i in
    string_as_const rng uu____3105 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3124 =
      let uu____3134 =
        let uu____3144 =
          let uu____3154 =
            let uu____3164 =
              let uu____3174 =
                let uu____3184 =
                  let uu____3194 =
                    let uu____3204 =
                      let uu____3214 =
                        let uu____3224 =
                          let uu____3234 =
                            let uu____3244 =
                              let uu____3254 =
                                let uu____3264 =
                                  let uu____3274 =
                                    let uu____3284 =
                                      let uu____3294 =
                                        let uu____3303 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3303, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3309 =
                                        let uu____3319 =
                                          let uu____3328 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3328, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3335 =
                                          let uu____3345 =
                                            let uu____3357 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3357,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3345] in
                                        uu____3319 :: uu____3335 in
                                      uu____3294 :: uu____3309 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3284 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3274 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3264 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3254 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3244 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3234 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3224 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3214 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3204 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3194 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3184 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3174 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3164 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3154 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3144 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3134 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3124 in
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
      let uu____3681 =
        let uu____3682 =
          let uu____3683 = FStar_Syntax_Syntax.as_arg c in [uu____3683] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3682 in
      uu____3681 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3707 =
              let uu____3716 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3716, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3725  ->
                        fun uu____3726  ->
                          match (uu____3725, uu____3726) with
                          | ((int_to_t1,x),(uu____3737,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3743 =
              let uu____3753 =
                let uu____3762 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3762, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3771  ->
                          fun uu____3772  ->
                            match (uu____3771, uu____3772) with
                            | ((int_to_t1,x),(uu____3783,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3789 =
                let uu____3799 =
                  let uu____3808 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3808, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3817  ->
                            fun uu____3818  ->
                              match (uu____3817, uu____3818) with
                              | ((int_to_t1,x),(uu____3829,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3799] in
              uu____3753 :: uu____3789 in
            uu____3707 :: uu____3743)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3895)::(a1,uu____3897)::(a2,uu____3899)::[] ->
        let uu____3928 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3928 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3930 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3930
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3935 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3935
         | uu____3940 -> None)
    | uu____3941 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3954)::(a1,uu____3956)::(a2,uu____3958)::[] ->
        let uu____3987 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3987 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_3991 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_3991.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_3991.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_3991.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_3998 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_3998.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_3998.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_3998.FStar_Syntax_Syntax.vars)
                })
         | uu____4003 -> None)
    | (_typ,uu____4005)::uu____4006::(a1,uu____4008)::(a2,uu____4010)::[] ->
        let uu____4047 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4047 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4051 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4051.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4051.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4051.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4058 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4058.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4058.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4058.FStar_Syntax_Syntax.vars)
                })
         | uu____4063 -> None)
    | uu____4064 -> failwith "Unexpected number of arguments" in
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
        (let uu___163_4133 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4133.tcenv);
           delta_level = (uu___163_4133.delta_level);
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
        let uu___164_4155 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4155.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4155.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4155.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4174 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4202 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4202
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4205;
                     FStar_Syntax_Syntax.pos = uu____4206;
                     FStar_Syntax_Syntax.vars = uu____4207;_},uu____4208);
                FStar_Syntax_Syntax.tk = uu____4209;
                FStar_Syntax_Syntax.pos = uu____4210;
                FStar_Syntax_Syntax.vars = uu____4211;_},args)
             ->
             let uu____4231 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4231
             then
               let uu____4232 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4232 with
                | (Some (true ),uu____4265)::(uu____4266,(arg,uu____4268))::[]
                    -> arg
                | (uu____4309,(arg,uu____4311))::(Some (true ),uu____4312)::[]
                    -> arg
                | (Some (false ),uu____4353)::uu____4354::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4392::(Some (false ),uu____4393)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4431 -> tm1)
             else
               (let uu____4441 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4441
                then
                  let uu____4442 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4442 with
                  | (Some (true ),uu____4475)::uu____4476::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4514::(Some (true ),uu____4515)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4553)::(uu____4554,(arg,uu____4556))::[]
                      -> arg
                  | (uu____4597,(arg,uu____4599))::(Some (false ),uu____4600)::[]
                      -> arg
                  | uu____4641 -> tm1
                else
                  (let uu____4651 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4651
                   then
                     let uu____4652 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4652 with
                     | uu____4685::(Some (true ),uu____4686)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4724)::uu____4725::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4763)::(uu____4764,(arg,uu____4766))::[]
                         -> arg
                     | uu____4807 -> tm1
                   else
                     (let uu____4817 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4817
                      then
                        let uu____4818 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4818 with
                        | (Some (true ),uu____4851)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4875)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4899 -> tm1
                      else
                        (let uu____4909 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4909
                         then
                           match args with
                           | (t,uu____4911)::[] ->
                               let uu____4924 =
                                 let uu____4925 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4925.FStar_Syntax_Syntax.n in
                               (match uu____4924 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4928::[],body,uu____4930) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4956 -> tm1)
                                | uu____4958 -> tm1)
                           | (uu____4959,Some (FStar_Syntax_Syntax.Implicit
                              uu____4960))::(t,uu____4962)::[] ->
                               let uu____4989 =
                                 let uu____4990 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4990.FStar_Syntax_Syntax.n in
                               (match uu____4989 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4993::[],body,uu____4995) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5021 -> tm1)
                                | uu____5023 -> tm1)
                           | uu____5024 -> tm1
                         else
                           (let uu____5031 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5031
                            then
                              match args with
                              | (t,uu____5033)::[] ->
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
                                        | uu____5078 -> tm1)
                                   | uu____5080 -> tm1)
                              | (uu____5081,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5082))::
                                  (t,uu____5084)::[] ->
                                  let uu____5111 =
                                    let uu____5112 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5112.FStar_Syntax_Syntax.n in
                                  (match uu____5111 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5115::[],body,uu____5117) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5143 -> tm1)
                                   | uu____5145 -> tm1)
                              | uu____5146 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5154;
                FStar_Syntax_Syntax.pos = uu____5155;
                FStar_Syntax_Syntax.vars = uu____5156;_},args)
             ->
             let uu____5172 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5172
             then
               let uu____5173 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5173 with
                | (Some (true ),uu____5206)::(uu____5207,(arg,uu____5209))::[]
                    -> arg
                | (uu____5250,(arg,uu____5252))::(Some (true ),uu____5253)::[]
                    -> arg
                | (Some (false ),uu____5294)::uu____5295::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5333::(Some (false ),uu____5334)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5372 -> tm1)
             else
               (let uu____5382 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5382
                then
                  let uu____5383 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5383 with
                  | (Some (true ),uu____5416)::uu____5417::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5455::(Some (true ),uu____5456)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5494)::(uu____5495,(arg,uu____5497))::[]
                      -> arg
                  | (uu____5538,(arg,uu____5540))::(Some (false ),uu____5541)::[]
                      -> arg
                  | uu____5582 -> tm1
                else
                  (let uu____5592 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5592
                   then
                     let uu____5593 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5593 with
                     | uu____5626::(Some (true ),uu____5627)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5665)::uu____5666::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5704)::(uu____5705,(arg,uu____5707))::[]
                         -> arg
                     | uu____5748 -> tm1
                   else
                     (let uu____5758 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5758
                      then
                        let uu____5759 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5759 with
                        | (Some (true ),uu____5792)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5816)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5840 -> tm1
                      else
                        (let uu____5850 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5850
                         then
                           match args with
                           | (t,uu____5852)::[] ->
                               let uu____5865 =
                                 let uu____5866 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5866.FStar_Syntax_Syntax.n in
                               (match uu____5865 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5869::[],body,uu____5871) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5897 -> tm1)
                                | uu____5899 -> tm1)
                           | (uu____5900,Some (FStar_Syntax_Syntax.Implicit
                              uu____5901))::(t,uu____5903)::[] ->
                               let uu____5930 =
                                 let uu____5931 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5931.FStar_Syntax_Syntax.n in
                               (match uu____5930 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5934::[],body,uu____5936) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5962 -> tm1)
                                | uu____5964 -> tm1)
                           | uu____5965 -> tm1
                         else
                           (let uu____5972 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5972
                            then
                              match args with
                              | (t,uu____5974)::[] ->
                                  let uu____5987 =
                                    let uu____5988 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5988.FStar_Syntax_Syntax.n in
                                  (match uu____5987 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5991::[],body,uu____5993) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6019 -> tm1)
                                   | uu____6021 -> tm1)
                              | (uu____6022,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6023))::
                                  (t,uu____6025)::[] ->
                                  let uu____6052 =
                                    let uu____6053 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6053.FStar_Syntax_Syntax.n in
                                  (match uu____6052 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6056::[],body,uu____6058) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6084 -> tm1)
                                   | uu____6086 -> tm1)
                              | uu____6087 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6094 -> tm1)
let is_norm_request hd1 args =
  let uu____6109 =
    let uu____6113 =
      let uu____6114 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6114.FStar_Syntax_Syntax.n in
    (uu____6113, args) in
  match uu____6109 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6119::uu____6120::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6123::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6125 -> false
let get_norm_request args =
  match args with
  | uu____6144::(tm,uu____6146)::[] -> tm
  | (tm,uu____6156)::[] -> tm
  | uu____6161 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6168  ->
    match uu___140_6168 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6170;
           FStar_Syntax_Syntax.pos = uu____6171;
           FStar_Syntax_Syntax.vars = uu____6172;_},uu____6173,uu____6174))::uu____6175
        -> true
    | uu____6181 -> false
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
            (fun uu____6299  ->
               let uu____6300 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6301 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6302 =
                 let uu____6303 =
                   let uu____6305 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6305 in
                 stack_to_string uu____6303 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6300
                 uu____6301 uu____6302);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6317 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6338 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6347 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6348 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6349;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6350;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6355;
                 FStar_Syntax_Syntax.fv_delta = uu____6356;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6360;
                 FStar_Syntax_Syntax.fv_delta = uu____6361;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6362);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6395 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6395.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6395.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6395.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6421 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6421) && (is_norm_request hd1 args))
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
                 let uu___166_6434 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6434.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6434.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6439;
                  FStar_Syntax_Syntax.pos = uu____6440;
                  FStar_Syntax_Syntax.vars = uu____6441;_},a1::a2::rest)
               ->
               let uu____6475 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6475 with
                | (hd1,uu____6486) ->
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
                    (FStar_Const.Const_reflect uu____6541);
                  FStar_Syntax_Syntax.tk = uu____6542;
                  FStar_Syntax_Syntax.pos = uu____6543;
                  FStar_Syntax_Syntax.vars = uu____6544;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6567 = FStar_List.tl stack1 in
               norm cfg env uu____6567 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6570;
                  FStar_Syntax_Syntax.pos = uu____6571;
                  FStar_Syntax_Syntax.vars = uu____6572;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6595 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6595 with
                | (reify_head,uu____6606) ->
                    let a1 =
                      let uu____6622 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6622 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6625);
                            FStar_Syntax_Syntax.tk = uu____6626;
                            FStar_Syntax_Syntax.pos = uu____6627;
                            FStar_Syntax_Syntax.vars = uu____6628;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6653 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6661 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6661
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6668 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6668
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6671 =
                      let uu____6675 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6675, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6671 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6684  ->
                         match uu___141_6684 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6687 =
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
                 if uu____6687 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6691 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6691 in
                  let uu____6692 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6692 with
                  | None  ->
                      (log cfg
                         (fun uu____6703  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6709  ->
                            let uu____6710 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6711 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6710 uu____6711);
                       (let t3 =
                          let uu____6713 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6713
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
                          | (UnivArgs (us',uu____6729))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6742 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6743 ->
                              let uu____6744 =
                                let uu____6745 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6745 in
                              failwith uu____6744
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6752 = lookup_bvar env x in
               (match uu____6752 with
                | Univ uu____6753 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6768 = FStar_ST.read r in
                      (match uu____6768 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6787  ->
                                 let uu____6788 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6789 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6788
                                   uu____6789);
                            (let uu____6790 =
                               let uu____6791 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6791.FStar_Syntax_Syntax.n in
                             match uu____6790 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6794 ->
                                 norm cfg env2 stack1 t'
                             | uu____6809 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6842)::uu____6843 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6848)::uu____6849 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6855,uu____6856))::stack_rest ->
                    (match c with
                     | Univ uu____6859 -> norm cfg (c :: env) stack_rest t1
                     | uu____6860 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6863::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6876  ->
                                         let uu____6877 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6877);
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
                                           (fun uu___142_6891  ->
                                              match uu___142_6891 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6892 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6894  ->
                                         let uu____6895 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6895);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6906  ->
                                         let uu____6907 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6907);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6908 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6915 ->
                                   let cfg1 =
                                     let uu___167_6923 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_6923.tcenv);
                                       delta_level =
                                         (uu___167_6923.delta_level);
                                       primitive_steps =
                                         (uu___167_6923.primitive_steps)
                                     } in
                                   let uu____6924 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6924)
                          | uu____6925::tl1 ->
                              (log cfg
                                 (fun uu____6935  ->
                                    let uu____6936 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6936);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_6960 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_6960.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6973  ->
                          let uu____6974 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6974);
                     norm cfg env stack2 t1)
                | (Debug uu____6975)::uu____6976 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6978 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6978
                    else
                      (let uu____6980 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6980 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7009 =
                                   let uu____7015 =
                                     let uu____7016 =
                                       let uu____7017 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7017 in
                                     FStar_All.pipe_right uu____7016
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7015
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____7009
                                   (fun _0_32  -> Some _0_32)
                             | uu____7042 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7056  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7061  ->
                                 let uu____7062 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7062);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7074 = cfg in
                               let uu____7075 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7074.steps);
                                 tcenv = (uu___169_7074.tcenv);
                                 delta_level = (uu___169_7074.delta_level);
                                 primitive_steps = uu____7075
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7085)::uu____7086 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7090 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7090
                    else
                      (let uu____7092 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7092 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7121 =
                                   let uu____7127 =
                                     let uu____7128 =
                                       let uu____7129 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7129 in
                                     FStar_All.pipe_right uu____7128
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7127
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7121
                                   (fun _0_34  -> Some _0_34)
                             | uu____7154 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7168  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7173  ->
                                 let uu____7174 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7174);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7186 = cfg in
                               let uu____7187 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7186.steps);
                                 tcenv = (uu___169_7186.tcenv);
                                 delta_level = (uu___169_7186.delta_level);
                                 primitive_steps = uu____7187
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7197)::uu____7198 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7204 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7204
                    else
                      (let uu____7206 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7206 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7235 =
                                   let uu____7241 =
                                     let uu____7242 =
                                       let uu____7243 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7243 in
                                     FStar_All.pipe_right uu____7242
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7241
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7235
                                   (fun _0_36  -> Some _0_36)
                             | uu____7268 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7282  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7287  ->
                                 let uu____7288 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7288);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7300 = cfg in
                               let uu____7301 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7300.steps);
                                 tcenv = (uu___169_7300.tcenv);
                                 delta_level = (uu___169_7300.delta_level);
                                 primitive_steps = uu____7301
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7311)::uu____7312 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7317 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7317
                    else
                      (let uu____7319 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7319 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7348 =
                                   let uu____7354 =
                                     let uu____7355 =
                                       let uu____7356 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7356 in
                                     FStar_All.pipe_right uu____7355
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7354
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7348
                                   (fun _0_38  -> Some _0_38)
                             | uu____7381 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7395  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7400  ->
                                 let uu____7401 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7401);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7413 = cfg in
                               let uu____7414 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7413.steps);
                                 tcenv = (uu___169_7413.tcenv);
                                 delta_level = (uu___169_7413.delta_level);
                                 primitive_steps = uu____7414
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7424)::uu____7425 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7435 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7435
                    else
                      (let uu____7437 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7437 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7466 =
                                   let uu____7472 =
                                     let uu____7473 =
                                       let uu____7474 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7474 in
                                     FStar_All.pipe_right uu____7473
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7472
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7466
                                   (fun _0_40  -> Some _0_40)
                             | uu____7499 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7513  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7518  ->
                                 let uu____7519 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7519);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7531 = cfg in
                               let uu____7532 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7531.steps);
                                 tcenv = (uu___169_7531.tcenv);
                                 delta_level = (uu___169_7531.delta_level);
                                 primitive_steps = uu____7532
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7542 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7542
                    else
                      (let uu____7544 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7544 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7573 =
                                   let uu____7579 =
                                     let uu____7580 =
                                       let uu____7581 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7581 in
                                     FStar_All.pipe_right uu____7580
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7579
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7573
                                   (fun _0_42  -> Some _0_42)
                             | uu____7606 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7620  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7625  ->
                                 let uu____7626 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7626);
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
                             ((let uu___170_7741 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7741.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7741.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7742 ->
                      let uu____7745 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7745)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7748 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7748 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7764 =
                          let uu____7765 =
                            let uu____7770 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7771 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7771.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7771.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7770) in
                          FStar_Syntax_Syntax.Tm_refine uu____7765 in
                        mk uu____7764 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7784 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7784
               else
                 (let uu____7786 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7786 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7792 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7798  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7792 c1 in
                      let t2 =
                        let uu____7805 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7805 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7848)::uu____7849 -> norm cfg env stack1 t11
                | (Arg uu____7854)::uu____7855 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7860;
                       FStar_Syntax_Syntax.pos = uu____7861;
                       FStar_Syntax_Syntax.vars = uu____7862;_},uu____7863,uu____7864))::uu____7865
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7871)::uu____7872 ->
                    norm cfg env stack1 t11
                | uu____7877 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7880  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7893 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7893
                        | FStar_Util.Inr c ->
                            let uu____7901 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7901 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7906 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7906)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7957,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7958;
                              FStar_Syntax_Syntax.lbunivs = uu____7959;
                              FStar_Syntax_Syntax.lbtyp = uu____7960;
                              FStar_Syntax_Syntax.lbeff = uu____7961;
                              FStar_Syntax_Syntax.lbdef = uu____7962;_}::uu____7963),uu____7964)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7990 =
                 (let uu____7991 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7991) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7992 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7992))) in
               if uu____7990
               then
                 let env1 =
                   let uu____7995 =
                     let uu____7996 =
                       let uu____8006 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8006,
                         false) in
                     Clos uu____7996 in
                   uu____7995 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8030 =
                    let uu____8033 =
                      let uu____8034 =
                        let uu____8035 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8035
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8034] in
                    FStar_Syntax_Subst.open_term uu____8033 body in
                  match uu____8030 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8041 = lb in
                        let uu____8042 =
                          let uu____8045 =
                            let uu____8046 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8046
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8045
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____8055 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8058 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8042;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8041.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8055;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8041.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8058
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8068  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8084 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8084
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8097 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8119  ->
                        match uu____8119 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8158 =
                                let uu___173_8159 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8159.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8159.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8158 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8097 with
                | (rec_env,memos,uu____8219) ->
                    let uu____8234 =
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
                             let uu____8276 =
                               let uu____8277 =
                                 let uu____8287 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8287, false) in
                               Clos uu____8277 in
                             uu____8276 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8325;
                             FStar_Syntax_Syntax.pos = uu____8326;
                             FStar_Syntax_Syntax.vars = uu____8327;_},uu____8328,uu____8329))::uu____8330
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8336 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8343 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8343
                        then
                          let uu___174_8344 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8344.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8344.primitive_steps)
                          }
                        else
                          (let uu___175_8346 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8346.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8346.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8348 =
                         let uu____8349 = FStar_Syntax_Subst.compress head1 in
                         uu____8349.FStar_Syntax_Syntax.n in
                       match uu____8348 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8363 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8363 with
                            | (uu____8364,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8368 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8375 =
                                         let uu____8376 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8376.FStar_Syntax_Syntax.n in
                                       match uu____8375 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8381,uu____8382))
                                           ->
                                           let uu____8391 =
                                             let uu____8392 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8392.FStar_Syntax_Syntax.n in
                                           (match uu____8391 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8397,msrc,uu____8399))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8408 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8408
                                            | uu____8409 -> None)
                                       | uu____8410 -> None in
                                     let uu____8411 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8411 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8415 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8415.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8415.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8415.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8416 =
                                            FStar_List.tl stack1 in
                                          let uu____8417 =
                                            let uu____8418 =
                                              let uu____8421 =
                                                let uu____8422 =
                                                  let uu____8430 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8430) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8422 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8421 in
                                            uu____8418 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8416 uu____8417
                                      | None  ->
                                          let uu____8447 =
                                            let uu____8448 = is_return body in
                                            match uu____8448 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8451;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8452;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8453;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8458 -> false in
                                          if uu____8447
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
                                               let uu____8478 =
                                                 let uu____8481 =
                                                   let uu____8482 =
                                                     let uu____8497 =
                                                       let uu____8499 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8499] in
                                                     (uu____8497, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8482 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8481 in
                                               uu____8478 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8532 =
                                                 let uu____8533 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8533.FStar_Syntax_Syntax.n in
                                               match uu____8532 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8539::uu____8540::[])
                                                   ->
                                                   let uu____8546 =
                                                     let uu____8549 =
                                                       let uu____8550 =
                                                         let uu____8555 =
                                                           let uu____8557 =
                                                             let uu____8558 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8558 in
                                                           let uu____8559 =
                                                             let uu____8561 =
                                                               let uu____8562
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8562 in
                                                             [uu____8561] in
                                                           uu____8557 ::
                                                             uu____8559 in
                                                         (bind1, uu____8555) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8550 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8549 in
                                                   uu____8546 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8574 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8580 =
                                                 let uu____8583 =
                                                   let uu____8584 =
                                                     let uu____8594 =
                                                       let uu____8596 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8597 =
                                                         let uu____8599 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8600 =
                                                           let uu____8602 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8603 =
                                                             let uu____8605 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8606 =
                                                               let uu____8608
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8609
                                                                 =
                                                                 let uu____8611
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8611] in
                                                               uu____8608 ::
                                                                 uu____8609 in
                                                             uu____8605 ::
                                                               uu____8606 in
                                                           uu____8602 ::
                                                             uu____8603 in
                                                         uu____8599 ::
                                                           uu____8600 in
                                                       uu____8596 ::
                                                         uu____8597 in
                                                     (bind_inst, uu____8594) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8584 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8583 in
                                               uu____8580 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8623 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8623 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8641 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8641 with
                            | (uu____8642,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8665 =
                                        let uu____8666 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8666.FStar_Syntax_Syntax.n in
                                      match uu____8665 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8672) -> t4
                                      | uu____8677 -> head2 in
                                    let uu____8678 =
                                      let uu____8679 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8679.FStar_Syntax_Syntax.n in
                                    match uu____8678 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8684 -> None in
                                  let uu____8685 = maybe_extract_fv head2 in
                                  match uu____8685 with
                                  | Some x when
                                      let uu____8691 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8691
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8695 =
                                          maybe_extract_fv head3 in
                                        match uu____8695 with
                                        | Some uu____8698 -> Some true
                                        | uu____8699 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8702 -> (head2, None) in
                                ((let is_arg_impure uu____8713 =
                                    match uu____8713 with
                                    | (e,q) ->
                                        let uu____8718 =
                                          let uu____8719 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8719.FStar_Syntax_Syntax.n in
                                        (match uu____8718 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8734 -> false) in
                                  let uu____8735 =
                                    let uu____8736 =
                                      let uu____8740 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8740 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8736 in
                                  if uu____8735
                                  then
                                    let uu____8743 =
                                      let uu____8744 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8744 in
                                    failwith uu____8743
                                  else ());
                                 (let uu____8746 =
                                    maybe_unfold_action head_app in
                                  match uu____8746 with
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
                                      let uu____8781 = FStar_List.tl stack1 in
                                      norm cfg env uu____8781 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8795 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8795 in
                           let uu____8796 = FStar_List.tl stack1 in
                           norm cfg env uu____8796 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8879  ->
                                     match uu____8879 with
                                     | (pat,wopt,tm) ->
                                         let uu____8917 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8917))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8943 = FStar_List.tl stack1 in
                           norm cfg env uu____8943 tm
                       | uu____8944 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8953;
                             FStar_Syntax_Syntax.pos = uu____8954;
                             FStar_Syntax_Syntax.vars = uu____8955;_},uu____8956,uu____8957))::uu____8958
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8964 -> false in
                    if should_reify
                    then
                      let uu____8965 = FStar_List.tl stack1 in
                      let uu____8966 =
                        let uu____8967 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8967 in
                      norm cfg env uu____8965 uu____8966
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8970 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8970
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_8976 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_8976.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_8976.primitive_steps)
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
                | uu____8978 ->
                    (match stack1 with
                     | uu____8979::uu____8980 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8984)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8999 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9009 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9009
                           | uu____9016 -> m in
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
              let uu____9028 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9028 with
              | (uu____9029,return_repr) ->
                  let return_inst =
                    let uu____9036 =
                      let uu____9037 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9037.FStar_Syntax_Syntax.n in
                    match uu____9036 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9043::[])
                        ->
                        let uu____9049 =
                          let uu____9052 =
                            let uu____9053 =
                              let uu____9058 =
                                let uu____9060 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9060] in
                              (return_tm, uu____9058) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9053 in
                          FStar_Syntax_Syntax.mk uu____9052 in
                        uu____9049 None e.FStar_Syntax_Syntax.pos
                    | uu____9072 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9075 =
                    let uu____9078 =
                      let uu____9079 =
                        let uu____9089 =
                          let uu____9091 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9092 =
                            let uu____9094 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9094] in
                          uu____9091 :: uu____9092 in
                        (return_inst, uu____9089) in
                      FStar_Syntax_Syntax.Tm_app uu____9079 in
                    FStar_Syntax_Syntax.mk uu____9078 in
                  uu____9075 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9107 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9107 with
               | None  ->
                   let uu____9109 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9109
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9110;
                     FStar_TypeChecker_Env.mtarget = uu____9111;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9112;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9123;
                     FStar_TypeChecker_Env.mtarget = uu____9124;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9125;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9143 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9143)
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
                (fun uu____9173  ->
                   match uu____9173 with
                   | (a,imp) ->
                       let uu____9180 = norm cfg env [] a in
                       (uu____9180, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9195 = comp1 in
            let uu____9198 =
              let uu____9199 =
                let uu____9205 = norm cfg env [] t in
                let uu____9206 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9205, uu____9206) in
              FStar_Syntax_Syntax.Total uu____9199 in
            {
              FStar_Syntax_Syntax.n = uu____9198;
              FStar_Syntax_Syntax.tk = (uu___178_9195.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9195.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9195.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9221 = comp1 in
            let uu____9224 =
              let uu____9225 =
                let uu____9231 = norm cfg env [] t in
                let uu____9232 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9231, uu____9232) in
              FStar_Syntax_Syntax.GTotal uu____9225 in
            {
              FStar_Syntax_Syntax.n = uu____9224;
              FStar_Syntax_Syntax.tk = (uu___179_9221.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9221.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9221.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9263  ->
                      match uu____9263 with
                      | (a,i) ->
                          let uu____9270 = norm cfg env [] a in
                          (uu____9270, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9275  ->
                      match uu___143_9275 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9279 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9279
                      | f -> f)) in
            let uu___180_9283 = comp1 in
            let uu____9286 =
              let uu____9287 =
                let uu___181_9288 = ct in
                let uu____9289 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9290 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9293 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9289;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9288.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9290;
                  FStar_Syntax_Syntax.effect_args = uu____9293;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9287 in
            {
              FStar_Syntax_Syntax.n = uu____9286;
              FStar_Syntax_Syntax.tk = (uu___180_9283.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9283.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9283.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9310 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9310.tcenv);
               delta_level = (uu___182_9310.delta_level);
               primitive_steps = (uu___182_9310.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9315 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9315 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9318 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9332 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9332.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9332.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9332.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9342 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9342
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9347 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9347.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9347.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9347.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9347.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9349 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9349.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9349.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9349.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9349.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9350 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9350.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9350.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9350.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9356 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9359  ->
        match uu____9359 with
        | (x,imp) ->
            let uu____9362 =
              let uu___187_9363 = x in
              let uu____9364 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9363.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9363.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9364
              } in
            (uu____9362, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9370 =
          FStar_List.fold_left
            (fun uu____9377  ->
               fun b  ->
                 match uu____9377 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9370 with | (nbs,uu____9394) -> FStar_List.rev nbs
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
            let uu____9411 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9411
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9416 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9416
               then
                 let uu____9420 =
                   let uu____9423 =
                     let uu____9424 =
                       let uu____9427 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9427 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9424 in
                   FStar_Util.Inl uu____9423 in
                 Some uu____9420
               else
                 (let uu____9431 =
                    let uu____9434 =
                      let uu____9435 =
                        let uu____9438 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9438 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9435 in
                    FStar_Util.Inl uu____9434 in
                  Some uu____9431))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9451 -> lopt
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
              ((let uu____9463 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9463
                then
                  let uu____9464 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9465 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9464
                    uu____9465
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9476 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9476.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9496  ->
                    let uu____9497 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9497);
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
              let uu____9534 =
                let uu___189_9535 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9535.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9535.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9535.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9534
          | (Arg (Univ uu____9540,uu____9541,uu____9542))::uu____9543 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9545,uu____9546))::uu____9547 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9559),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9575  ->
                    let uu____9576 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9576);
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
                 (let uu____9587 = FStar_ST.read m in
                  match uu____9587 with
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
                  | Some (uu____9613,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9635 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9635
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9642  ->
                    let uu____9643 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9643);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9648 =
                  log cfg
                    (fun uu____9650  ->
                       let uu____9651 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9652 =
                         let uu____9653 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9660  ->
                                   match uu____9660 with
                                   | (p,uu____9666,uu____9667) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9653
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9651 uu____9652);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9677  ->
                               match uu___144_9677 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9678 -> false)) in
                     let steps' =
                       let uu____9681 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9681
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9684 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9684.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9684.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9718 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9734 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9768  ->
                                   fun uu____9769  ->
                                     match (uu____9768, uu____9769) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9834 = norm_pat env3 p1 in
                                         (match uu____9834 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9734 with
                          | (pats1,env3) ->
                              ((let uu___191_9900 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_9900.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_9900.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_9914 = x in
                           let uu____9915 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_9914.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_9914.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9915
                           } in
                         ((let uu___193_9921 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_9921.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_9921.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_9926 = x in
                           let uu____9927 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_9926.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_9926.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9927
                           } in
                         ((let uu___195_9933 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_9933.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_9933.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_9943 = x in
                           let uu____9944 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_9943.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_9943.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9944
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_9951 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_9951.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_9951.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9955 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9958 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9958 with
                                 | (p,wopt,e) ->
                                     let uu____9976 = norm_pat env1 p in
                                     (match uu____9976 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10000 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10000 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10005 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10005) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10015) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10020 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10021;
                        FStar_Syntax_Syntax.fv_delta = uu____10022;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10026;
                        FStar_Syntax_Syntax.fv_delta = uu____10027;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10028);_}
                      -> true
                  | uu____10035 -> false in
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
                  let uu____10134 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10134 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10166 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10168 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10170 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10182 ->
                                let uu____10183 =
                                  let uu____10184 = is_cons head1 in
                                  Prims.op_Negation uu____10184 in
                                FStar_Util.Inr uu____10183)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10198 =
                             let uu____10199 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10199.FStar_Syntax_Syntax.n in
                           (match uu____10198 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10206 ->
                                let uu____10207 =
                                  let uu____10208 = is_cons head1 in
                                  Prims.op_Negation uu____10208 in
                                FStar_Util.Inr uu____10207))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10242)::rest_a,(p1,uu____10245)::rest_p) ->
                      let uu____10273 = matches_pat t1 p1 in
                      (match uu____10273 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10287 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10358 = matches_pat scrutinee1 p1 in
                      (match uu____10358 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10368  ->
                                 let uu____10369 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10370 =
                                   let uu____10371 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10371
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10369 uu____10370);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10380 =
                                        let uu____10381 =
                                          let uu____10391 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10391, false) in
                                        Clos uu____10381 in
                                      uu____10380 :: env2) env1 s in
                             let uu____10414 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10414))) in
                let uu____10415 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10415
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10429  ->
                match uu___145_10429 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10432 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10436 -> d in
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
            let uu___198_10456 = config s e in
            {
              steps = (uu___198_10456.steps);
              tcenv = (uu___198_10456.tcenv);
              delta_level = (uu___198_10456.delta_level);
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
      fun t  -> let uu____10475 = config s e in norm_comp uu____10475 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10482 = config [] env in norm_universe uu____10482 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10489 = config [] env in ghost_to_pure_aux uu____10489 [] c
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
        let uu____10501 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10501 in
      let uu____10502 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10502
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10504 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10504.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10504.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10505  ->
                    let uu____10506 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10506))
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
            ((let uu____10519 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10519);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10528 = config [AllowUnboundUniverses] env in
          norm_comp uu____10528 [] c
        with
        | e ->
            ((let uu____10532 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10532);
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
                   let uu____10569 =
                     let uu____10570 =
                       let uu____10575 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10575) in
                     FStar_Syntax_Syntax.Tm_refine uu____10570 in
                   mk uu____10569 t01.FStar_Syntax_Syntax.pos
               | uu____10580 -> t2)
          | uu____10581 -> t2 in
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
        let uu____10603 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10603 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10619 ->
                 let uu____10623 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10623 with
                  | (actuals,uu____10634,uu____10635) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10661 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10661 with
                         | (binders,args) ->
                             let uu____10671 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10674 =
                               let uu____10681 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10681
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10671
                               uu____10674)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10717 =
        let uu____10721 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10721, (t.FStar_Syntax_Syntax.n)) in
      match uu____10717 with
      | (Some sort,uu____10728) ->
          let uu____10730 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10730
      | (uu____10731,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10735 ->
          let uu____10739 = FStar_Syntax_Util.head_and_args t in
          (match uu____10739 with
           | (head1,args) ->
               let uu____10765 =
                 let uu____10766 = FStar_Syntax_Subst.compress head1 in
                 uu____10766.FStar_Syntax_Syntax.n in
               (match uu____10765 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10769,thead) ->
                    let uu____10783 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10783 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10818 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_10822 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_10822.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_10822.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_10822.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_10822.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_10822.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_10822.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_10822.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_10822.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_10822.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_10822.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_10822.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_10822.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_10822.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_10822.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_10822.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_10822.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_10822.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_10822.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_10822.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_10822.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_10822.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_10822.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____10818 with
                            | (uu____10823,ty,uu____10825) ->
                                eta_expand_with_type env t ty))
                | uu____10826 ->
                    let uu____10827 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_10831 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_10831.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_10831.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_10831.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_10831.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_10831.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_10831.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_10831.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_10831.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_10831.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_10831.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_10831.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_10831.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_10831.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_10831.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_10831.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_10831.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_10831.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_10831.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_10831.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_10831.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_10831.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_10831.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____10827 with
                     | (uu____10832,ty,uu____10834) ->
                         eta_expand_with_type env t ty)))