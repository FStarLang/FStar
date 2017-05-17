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
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option;}
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
  fun uu___138_223  ->
    match uu___138_223 with
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
      FStar_Util.either Prims.option* FStar_Range.range)
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
  fun uu___139_671  ->
    match uu___139_671 with
    | Arg (c,uu____673,uu____674) ->
        let uu____675 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____675
    | MemoLazy uu____676 -> "MemoLazy"
    | Abs (uu____680,bs,uu____682,uu____683,uu____684) ->
        let uu____691 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____691
    | UnivArgs uu____696 -> "UnivArgs"
    | Match uu____700 -> "Match"
    | App (t,uu____705,uu____706) ->
        let uu____707 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____707
    | Meta (m,uu____709) -> "Meta"
    | Let uu____710 -> "Let"
    | Steps (uu____715,uu____716,uu____717) -> "Steps"
    | Debug t ->
        let uu____723 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____723
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____729 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____729 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____743 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____743 then f () else ()
let is_empty uu___140_752 =
  match uu___140_752 with | [] -> true | uu____754 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____772 ->
      let uu____773 =
        let uu____774 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____774 in
      failwith uu____773
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
          let uu____805 =
            FStar_List.fold_left
              (fun uu____814  ->
                 fun u1  ->
                   match uu____814 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____829 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____829 with
                        | (k_u,n1) ->
                            let uu____838 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____838
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____805 with
          | (uu____848,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____864 = FStar_List.nth env x in
                 match uu____864 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____867 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____871 ->
                   let uu____872 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____872
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____882 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____882 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____893 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____893 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____898 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____901 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____901 with
                                  | (uu____904,m) -> n1 <= m)) in
                        if uu____898 then rest1 else us1
                    | uu____908 -> us1)
               | uu____911 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____914 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____914 in
        let uu____916 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____916
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____918 = aux u in
           match uu____918 with
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
          (fun uu____1015  ->
             let uu____1016 = FStar_Syntax_Print.tag_of_term t in
             let uu____1017 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1016
               uu____1017);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1018 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1021 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1045 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1055 =
                    let uu____1056 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1056 in
                  mk uu____1055 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1063 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1063
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1065 = lookup_bvar env x in
                  (match uu____1065 with
                   | Univ uu____1066 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1070) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1138 = closures_as_binders_delayed cfg env bs in
                  (match uu____1138 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1158 =
                         let uu____1159 =
                           let uu____1174 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1174) in
                         FStar_Syntax_Syntax.Tm_abs uu____1159 in
                       mk uu____1158 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1204 = closures_as_binders_delayed cfg env bs in
                  (match uu____1204 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1235 =
                    let uu____1242 =
                      let uu____1246 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1246] in
                    closures_as_binders_delayed cfg env uu____1242 in
                  (match uu____1235 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1260 =
                         let uu____1261 =
                           let uu____1266 =
                             let uu____1267 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1267 Prims.fst in
                           (uu____1266, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1261 in
                       mk uu____1260 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1335 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1335
                    | FStar_Util.Inr c ->
                        let uu____1349 = close_comp cfg env c in
                        FStar_Util.Inr uu____1349 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1364 =
                    let uu____1365 =
                      let uu____1383 = closure_as_term_delayed cfg env t11 in
                      (uu____1383, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1365 in
                  mk uu____1364 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1421 =
                    let uu____1422 =
                      let uu____1427 = closure_as_term_delayed cfg env t' in
                      let uu____1430 =
                        let uu____1431 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1431 in
                      (uu____1427, uu____1430) in
                    FStar_Syntax_Syntax.Tm_meta uu____1422 in
                  mk uu____1421 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1473 =
                    let uu____1474 =
                      let uu____1479 = closure_as_term_delayed cfg env t' in
                      let uu____1482 =
                        let uu____1483 =
                          let uu____1488 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1488) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1483 in
                      (uu____1479, uu____1482) in
                    FStar_Syntax_Syntax.Tm_meta uu____1474 in
                  mk uu____1473 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1507 =
                    let uu____1508 =
                      let uu____1513 = closure_as_term_delayed cfg env t' in
                      let uu____1516 =
                        let uu____1517 =
                          let uu____1523 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1523) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1517 in
                      (uu____1513, uu____1516) in
                    FStar_Syntax_Syntax.Tm_meta uu____1508 in
                  mk uu____1507 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1536 =
                    let uu____1537 =
                      let uu____1542 = closure_as_term_delayed cfg env t' in
                      (uu____1542, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1537 in
                  mk uu____1536 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1563  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1574 -> body
                    | FStar_Util.Inl uu____1575 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___153_1577 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___153_1577.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___153_1577.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___153_1577.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1584,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1608  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1613 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1613
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1617  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___154_1620 = lb in
                    let uu____1621 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1624 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___154_1620.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___154_1620.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1621;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___154_1620.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1624
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1635  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1690 =
                    match uu____1690 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1736 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                              let uu____1756 = norm_pat env2 hd1 in
                              (match uu____1756 with
                               | (hd2,env') ->
                                   let tl2 =
                                     FStar_All.pipe_right tl1
                                       (FStar_List.map
                                          (fun p1  ->
                                             let uu____1792 =
                                               norm_pat env2 p1 in
                                             Prims.fst uu____1792)) in
                                   ((let uu___155_1804 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___155_1804.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___155_1804.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1821 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1855  ->
                                        fun uu____1856  ->
                                          match (uu____1855, uu____1856) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1921 =
                                                norm_pat env3 p1 in
                                              (match uu____1921 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1821 with
                               | (pats1,env3) ->
                                   ((let uu___156_1987 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___156_1987.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___156_1987.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___157_2001 = x in
                                let uu____2002 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_2001.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_2001.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2002
                                } in
                              ((let uu___158_2008 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_2008.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_2008.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___159_2013 = x in
                                let uu____2014 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___159_2013.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___159_2013.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2014
                                } in
                              ((let uu___160_2020 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___160_2020.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___160_2020.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___161_2030 = x in
                                let uu____2031 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___161_2030.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___161_2030.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2031
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___162_2038 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___162_2038.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___162_2038.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2041 = norm_pat env1 pat in
                        (match uu____2041 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2065 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2065 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2070 =
                    let uu____2071 =
                      let uu____2087 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2087) in
                    FStar_Syntax_Syntax.Tm_match uu____2071 in
                  mk uu____2070 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2140 -> closure_as_term cfg env t
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
        | uu____2156 ->
            FStar_List.map
              (fun uu____2166  ->
                 match uu____2166 with
                 | (x,imp) ->
                     let uu____2181 = closure_as_term_delayed cfg env x in
                     (uu____2181, imp)) args
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
        let uu____2193 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2217  ->
                  fun uu____2218  ->
                    match (uu____2217, uu____2218) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___163_2262 = b in
                          let uu____2263 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___163_2262.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___163_2262.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2263
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2193 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2310 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2322 = closure_as_term_delayed cfg env t in
                 let uu____2323 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2322 uu____2323
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2333 = closure_as_term_delayed cfg env t in
                 let uu____2334 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2333 uu____2334
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
                        (fun uu___141_2350  ->
                           match uu___141_2350 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2354 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2354
                           | f -> f)) in
                 let uu____2358 =
                   let uu___164_2359 = c1 in
                   let uu____2360 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2360;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___164_2359.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2358)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___142_2364  ->
            match uu___142_2364 with
            | FStar_Syntax_Syntax.DECREASES uu____2365 -> false
            | uu____2368 -> true))
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
            let uu____2396 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2396
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2413 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2413
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2439 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2463 =
      let uu____2464 =
        let uu____2470 = FStar_Util.string_of_int i in (uu____2470, None) in
      FStar_Const.Const_int uu____2464 in
    const_as_tm uu____2463 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2497 =
    match uu____2497 with
    | (a,uu____2502) ->
        let uu____2504 =
          let uu____2505 = FStar_Syntax_Subst.compress a in
          uu____2505.FStar_Syntax_Syntax.n in
        (match uu____2504 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2515 = FStar_Util.int_of_string i in Some uu____2515
         | uu____2516 -> None) in
  let arg_as_bounded_int uu____2525 =
    match uu____2525 with
    | (a,uu____2532) ->
        let uu____2536 =
          let uu____2537 = FStar_Syntax_Subst.compress a in
          uu____2537.FStar_Syntax_Syntax.n in
        (match uu____2536 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2544;
                FStar_Syntax_Syntax.pos = uu____2545;
                FStar_Syntax_Syntax.vars = uu____2546;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2548;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2549;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2550;_},uu____2551)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2582 =
               let uu____2585 = FStar_Util.int_of_string i in
               (fv1, uu____2585) in
             Some uu____2582
         | uu____2588 -> None) in
  let arg_as_bool uu____2597 =
    match uu____2597 with
    | (a,uu____2602) ->
        let uu____2604 =
          let uu____2605 = FStar_Syntax_Subst.compress a in
          uu____2605.FStar_Syntax_Syntax.n in
        (match uu____2604 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2610 -> None) in
  let arg_as_char uu____2617 =
    match uu____2617 with
    | (a,uu____2622) ->
        let uu____2624 =
          let uu____2625 = FStar_Syntax_Subst.compress a in
          uu____2625.FStar_Syntax_Syntax.n in
        (match uu____2624 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2630 -> None) in
  let arg_as_string uu____2637 =
    match uu____2637 with
    | (a,uu____2642) ->
        let uu____2644 =
          let uu____2645 = FStar_Syntax_Subst.compress a in
          uu____2645.FStar_Syntax_Syntax.n in
        (match uu____2644 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2650)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2653 -> None) in
  let arg_as_list f uu____2674 =
    match uu____2674 with
    | (a,uu____2683) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2702 -> None
          | (Some x)::xs ->
              let uu____2712 = sequence xs in
              (match uu____2712 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2723 = FStar_Syntax_Util.list_elements a in
        (match uu____2723 with
         | None  -> None
         | Some elts ->
             let uu____2733 =
               FStar_List.map
                 (fun x  ->
                    let uu____2738 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2738) elts in
             sequence uu____2733) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2768 = f a in Some uu____2768
    | uu____2769 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2808 = f a0 a1 in Some uu____2808
    | uu____2809 -> None in
  let unary_op as_a f r args =
    let uu____2853 = FStar_List.map as_a args in lift_unary (f r) uu____2853 in
  let binary_op as_a f r args =
    let uu____2903 = FStar_List.map as_a args in lift_binary (f r) uu____2903 in
  let as_primitive_step uu____2920 =
    match uu____2920 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2958 = f x in int_as_const r uu____2958) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2981 = f x y in int_as_const r uu____2981) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2998 = f x in bool_as_const r uu____2998) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3021 = f x y in bool_as_const r uu____3021) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3044 = f x y in string_as_const r uu____3044) in
  let list_of_string' rng s =
    let name l =
      let uu____3058 =
        let uu____3059 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3059 in
      mk uu____3058 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3069 =
      let uu____3071 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3071 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3069 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_of_int1 rng i =
    let uu____3104 = FStar_Util.string_of_int i in
    string_as_const rng uu____3104 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3120 = FStar_Util.string_of_int i in
    string_as_const rng uu____3120 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3139 =
      let uu____3149 =
        let uu____3159 =
          let uu____3169 =
            let uu____3179 =
              let uu____3189 =
                let uu____3199 =
                  let uu____3209 =
                    let uu____3219 =
                      let uu____3229 =
                        let uu____3239 =
                          let uu____3249 =
                            let uu____3259 =
                              let uu____3269 =
                                let uu____3279 =
                                  let uu____3289 =
                                    let uu____3299 =
                                      let uu____3309 =
                                        let uu____3318 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3318, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3324 =
                                        let uu____3334 =
                                          let uu____3343 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3343, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        [uu____3334] in
                                      uu____3309 :: uu____3324 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3299 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3289 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3279 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3269 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3259 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3249 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3239 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3229 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3219 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3209 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3199 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3189 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3179 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3169 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3159 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3149 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3139 in
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
      let uu____3651 =
        let uu____3652 =
          let uu____3653 = FStar_Syntax_Syntax.as_arg c in [uu____3653] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3652 in
      uu____3651 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3677 =
              let uu____3686 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3686, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3695  ->
                        fun uu____3696  ->
                          match (uu____3695, uu____3696) with
                          | ((int_to_t1,x),(uu____3707,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3713 =
              let uu____3723 =
                let uu____3732 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3732, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3741  ->
                          fun uu____3742  ->
                            match (uu____3741, uu____3742) with
                            | ((int_to_t1,x),(uu____3753,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3759 =
                let uu____3769 =
                  let uu____3778 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3778, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3787  ->
                            fun uu____3788  ->
                              match (uu____3787, uu____3788) with
                              | ((int_to_t1,x),(uu____3799,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3769] in
              uu____3723 :: uu____3759 in
            uu____3677 :: uu____3713)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3865)::(a1,uu____3867)::(a2,uu____3869)::[] ->
        let uu____3898 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3898 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3900 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3900
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3905 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3905
         | uu____3910 -> None)
    | uu____3911 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,_)::(a1,_)::(a2,_)::[]|(_typ,_)::_::(a1,_)::(a2,_)::[] ->
        let uu____3993 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3993 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___165_3997 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_3997.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_3997.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_3997.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___166_4004 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_4004.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___166_4004.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_4004.FStar_Syntax_Syntax.vars)
                })
         | uu____4009 -> None)
    | uu____4010 -> failwith "Unexpected number of arguments" in
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
      let uu____4021 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4021
      then tm
      else
        (let uu____4023 = FStar_Syntax_Util.head_and_args tm in
         match uu____4023 with
         | (head1,args) ->
             let uu____4049 =
               let uu____4050 = FStar_Syntax_Util.un_uinst head1 in
               uu____4050.FStar_Syntax_Syntax.n in
             (match uu____4049 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4054 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4054 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4066 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4066 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4069 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___167_4076 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___167_4076.tcenv);
           delta_level = (uu___167_4076.delta_level);
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
        let uu___168_4098 = t in
        {
          FStar_Syntax_Syntax.n = (uu___168_4098.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___168_4098.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___168_4098.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4117 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____4144 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4144
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
             let uu____4184 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4184
             then
               let uu____4185 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4185 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4351 -> tm)
             else
               (let uu____4361 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4361
                then
                  let uu____4362 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4362 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____4528 -> tm
                else
                  (let uu____4538 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4538
                   then
                     let uu____4539 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4539 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4628)::(uu____4629,(arg,uu____4631))::[]
                         -> arg
                     | uu____4672 -> tm
                   else
                     (let uu____4682 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4682
                      then
                        let uu____4683 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4683 with
                        | (Some (true ),uu____4716)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4740)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4764 -> tm
                      else
                        (let uu____4774 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4774
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____4815 =
                                 let uu____4816 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4816.FStar_Syntax_Syntax.n in
                               (match uu____4815 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4819::[],body,uu____4821) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4847 -> tm)
                                | uu____4849 -> tm)
                           | uu____4850 -> tm
                         else
                           (let uu____4857 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4857
                            then
                              match args with
                              | (t,_)::[]
                                |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                                (t,_)::[] ->
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
                              | uu____4933 -> tm
                            else reduce_equality cfg tm)))))
         | uu____4940 -> tm)
let is_norm_request hd1 args =
  let uu____4955 =
    let uu____4959 =
      let uu____4960 = FStar_Syntax_Util.un_uinst hd1 in
      uu____4960.FStar_Syntax_Syntax.n in
    (uu____4959, args) in
  match uu____4955 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4965::uu____4966::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4969::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4971 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____5004 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___143_5011  ->
    match uu___143_5011 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____5013;
           FStar_Syntax_Syntax.pos = uu____5014;
           FStar_Syntax_Syntax.vars = uu____5015;_},uu____5016,uu____5017))::uu____5018
        -> true
    | uu____5024 -> false
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
            (fun uu____5139  ->
               let uu____5140 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____5141 = FStar_Syntax_Print.term_to_string t1 in
               let uu____5142 =
                 let uu____5143 =
                   let uu____5145 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____5145 in
                 stack_to_string uu____5143 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____5140
                 uu____5141 uu____5142);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____5157 ->
               failwith "Impossible: got a delayed substitution"
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
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___169_5214 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___169_5214.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___169_5214.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___169_5214.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____5240 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____5240) && (is_norm_request hd1 args))
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
                 let uu___170_5253 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___170_5253.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___170_5253.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____5258;
                  FStar_Syntax_Syntax.pos = uu____5259;
                  FStar_Syntax_Syntax.vars = uu____5260;_},a1::a2::rest)
               ->
               let uu____5294 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5294 with
                | (hd1,uu____5305) ->
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
                    (FStar_Const.Const_reflect uu____5360);
                  FStar_Syntax_Syntax.tk = uu____5361;
                  FStar_Syntax_Syntax.pos = uu____5362;
                  FStar_Syntax_Syntax.vars = uu____5363;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____5386 = FStar_List.tl stack1 in
               norm cfg env uu____5386 (Prims.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____5389;
                  FStar_Syntax_Syntax.pos = uu____5390;
                  FStar_Syntax_Syntax.vars = uu____5391;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____5414 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5414 with
                | (reify_head,uu____5425) ->
                    let a1 =
                      let uu____5441 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____5441 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____5444);
                            FStar_Syntax_Syntax.tk = uu____5445;
                            FStar_Syntax_Syntax.pos = uu____5446;
                            FStar_Syntax_Syntax.vars = uu____5447;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____5472 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____5480 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____5480
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____5487 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____5487
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____5490 =
                      let uu____5494 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____5494, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____5490 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___144_5503  ->
                         match uu___144_5503 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____5506 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     (((((((FStar_Syntax_Syntax.fv_eq_lid f
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
                             FStar_Syntax_Const.exists_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Syntax_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Syntax_Const.false_lid)) in
                 if uu____5506 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____5510 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____5510 in
                  let uu____5511 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____5511 with
                  | None  ->
                      (log cfg
                         (fun uu____5522  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____5528  ->
                            let uu____5529 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____5530 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____5529 uu____5530);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____5537))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____5550 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____5551 ->
                              let uu____5552 =
                                let uu____5553 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____5553 in
                              failwith uu____5552
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____5560 = lookup_bvar env x in
               (match uu____5560 with
                | Univ uu____5561 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____5576 = FStar_ST.read r in
                      (match uu____5576 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____5595  ->
                                 let uu____5596 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____5597 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____5596
                                   uu____5597);
                            (let uu____5598 =
                               let uu____5599 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____5599.FStar_Syntax_Syntax.n in
                             match uu____5598 with
                             | FStar_Syntax_Syntax.Tm_abs uu____5602 ->
                                 norm cfg env2 stack1 t'
                             | uu____5617 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____5650)::uu____5651 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____5656)::uu____5657 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____5663,uu____5664))::stack_rest ->
                    (match c with
                     | Univ uu____5667 -> norm cfg (c :: env) stack_rest t1
                     | uu____5668 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____5671::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____5684  ->
                                         let uu____5685 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5685);
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
                                           (fun uu___145_5699  ->
                                              match uu___145_5699 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____5700 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____5702  ->
                                         let uu____5703 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5703);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____5714  ->
                                         let uu____5715 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5715);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____5716 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____5723 ->
                                   let cfg1 =
                                     let uu___171_5731 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___171_5731.tcenv);
                                       delta_level =
                                         (uu___171_5731.delta_level);
                                       primitive_steps =
                                         (uu___171_5731.primitive_steps)
                                     } in
                                   let uu____5732 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____5732)
                          | uu____5733::tl1 ->
                              (log cfg
                                 (fun uu____5743  ->
                                    let uu____5744 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____5744);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___172_5768 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___172_5768.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____5781  ->
                          let uu____5782 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5782);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____5793 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5793
                    else
                      (let uu____5795 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____5795 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____5824 =
                                   let uu____5830 =
                                     let uu____5831 =
                                       let uu____5832 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____5832 in
                                     FStar_All.pipe_right uu____5831
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____5830
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____5824
                                   (fun _0_32  -> Some _0_32)
                             | uu____5857 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5871  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5876  ->
                                 let uu____5877 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5877);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___173_5887 = cfg in
                               let uu____5888 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___173_5887.steps);
                                 tcenv = (uu___173_5887.tcenv);
                                 delta_level = (uu___173_5887.delta_level);
                                 primitive_steps = uu____5888
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
                      (fun uu____5920  ->
                         fun stack2  ->
                           match uu____5920 with
                           | (a,aq) ->
                               let uu____5928 =
                                 let uu____5929 =
                                   let uu____5933 =
                                     let uu____5934 =
                                       let uu____5944 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5944, false) in
                                     Clos uu____5934 in
                                   (uu____5933, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5929 in
                               uu____5928 :: stack2) args) in
               (log cfg
                  (fun uu____5966  ->
                     let uu____5967 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5967);
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
                             ((let uu___174_5988 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___174_5988.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___174_5988.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____5989 ->
                      let uu____5992 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5992)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____5995 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____5995 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____6011 =
                          let uu____6012 =
                            let uu____6017 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___175_6018 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___175_6018.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___175_6018.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____6017) in
                          FStar_Syntax_Syntax.Tm_refine uu____6012 in
                        mk uu____6011 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____6031 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____6031
               else
                 (let uu____6033 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____6033 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____6039 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____6045  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____6039 c1 in
                      let t2 =
                        let uu____6052 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____6052 c2 in
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
                | uu____6109 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____6112  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____6125 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____6125
                        | FStar_Util.Inr c ->
                            let uu____6133 = norm_comp cfg env c in
                            FStar_Util.Inr uu____6133 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____6138 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____6138)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____6189,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____6190;
                              FStar_Syntax_Syntax.lbunivs = uu____6191;
                              FStar_Syntax_Syntax.lbtyp = uu____6192;
                              FStar_Syntax_Syntax.lbeff = uu____6193;
                              FStar_Syntax_Syntax.lbdef = uu____6194;_}::uu____6195),uu____6196)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____6222 =
                 (let uu____6223 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____6223) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____6224 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____6224))) in
               if uu____6222
               then
                 let env1 =
                   let uu____6227 =
                     let uu____6228 =
                       let uu____6238 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____6238,
                         false) in
                     Clos uu____6228 in
                   uu____6227 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____6262 =
                    let uu____6265 =
                      let uu____6266 =
                        let uu____6267 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____6267
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____6266] in
                    FStar_Syntax_Subst.open_term uu____6265 body in
                  match uu____6262 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___176_6273 = lb in
                        let uu____6274 =
                          let uu____6277 =
                            let uu____6278 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____6278 Prims.fst in
                          FStar_All.pipe_right uu____6277
                            (fun _0_33  -> FStar_Util.Inl _0_33) in
                        let uu____6287 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____6290 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____6274;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___176_6273.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6287;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___176_6273.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6290
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____6300  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____6316 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____6316
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____6329 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____6351  ->
                        match uu____6351 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____6390 =
                                let uu___177_6391 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___177_6391.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___177_6391.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____6390 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____6329 with
                | (rec_env,memos,uu____6451) ->
                    let uu____6466 =
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
                             let uu____6508 =
                               let uu____6509 =
                                 let uu____6519 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____6519, false) in
                               Clos uu____6509 in
                             uu____6508 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____6557;
                             FStar_Syntax_Syntax.pos = uu____6558;
                             FStar_Syntax_Syntax.vars = uu____6559;_},uu____6560,uu____6561))::uu____6562
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6568 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____6575 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____6575
                        then
                          let uu___178_6576 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___178_6576.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___178_6576.primitive_steps)
                          }
                        else
                          (let uu___179_6578 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___179_6578.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___179_6578.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____6580 =
                         let uu____6581 = FStar_Syntax_Subst.compress head1 in
                         uu____6581.FStar_Syntax_Syntax.n in
                       match uu____6580 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6595 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6595 with
                            | (uu____6596,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____6600 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____6607 =
                                         let uu____6608 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____6608.FStar_Syntax_Syntax.n in
                                       match uu____6607 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____6613,uu____6614))
                                           ->
                                           let uu____6623 =
                                             let uu____6624 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____6624.FStar_Syntax_Syntax.n in
                                           (match uu____6623 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____6629,msrc,uu____6631))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____6640 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____6640
                                            | uu____6641 -> None)
                                       | uu____6642 -> None in
                                     let uu____6643 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____6643 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___180_6647 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___180_6647.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___180_6647.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___180_6647.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____6648 =
                                            FStar_List.tl stack1 in
                                          let uu____6649 =
                                            let uu____6650 =
                                              let uu____6653 =
                                                let uu____6654 =
                                                  let uu____6662 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____6662) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____6654 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6653 in
                                            uu____6650 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____6648 uu____6649
                                      | None  ->
                                          let uu____6679 =
                                            let uu____6680 = is_return body in
                                            match uu____6680 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6683;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6684;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6685;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____6690 -> false in
                                          if uu____6679
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
                                               let uu____6710 =
                                                 let uu____6713 =
                                                   let uu____6714 =
                                                     let uu____6729 =
                                                       let uu____6731 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6731] in
                                                     (uu____6729, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____6714 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6713 in
                                               uu____6710 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____6764 =
                                                 let uu____6765 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____6765.FStar_Syntax_Syntax.n in
                                               match uu____6764 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____6771::uu____6772::[])
                                                   ->
                                                   let uu____6778 =
                                                     let uu____6781 =
                                                       let uu____6782 =
                                                         let uu____6787 =
                                                           let uu____6789 =
                                                             let uu____6790 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____6790 in
                                                           let uu____6791 =
                                                             let uu____6793 =
                                                               let uu____6794
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____6794 in
                                                             [uu____6793] in
                                                           uu____6789 ::
                                                             uu____6791 in
                                                         (bind1, uu____6787) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____6782 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6781 in
                                                   uu____6778 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____6806 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____6812 =
                                                 let uu____6815 =
                                                   let uu____6816 =
                                                     let uu____6826 =
                                                       let uu____6828 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____6829 =
                                                         let uu____6831 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____6832 =
                                                           let uu____6834 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____6835 =
                                                             let uu____6837 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____6838 =
                                                               let uu____6840
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____6841
                                                                 =
                                                                 let uu____6843
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____6843] in
                                                               uu____6840 ::
                                                                 uu____6841 in
                                                             uu____6837 ::
                                                               uu____6838 in
                                                           uu____6834 ::
                                                             uu____6835 in
                                                         uu____6831 ::
                                                           uu____6832 in
                                                       uu____6828 ::
                                                         uu____6829 in
                                                     (bind_inst, uu____6826) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6816 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6815 in
                                               uu____6812 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____6855 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____6855 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6873 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6873 with
                            | (uu____6874,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6897 =
                                        let uu____6898 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6898.FStar_Syntax_Syntax.n in
                                      match uu____6897 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6904) -> t4
                                      | uu____6909 -> head2 in
                                    let uu____6910 =
                                      let uu____6911 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____6911.FStar_Syntax_Syntax.n in
                                    match uu____6910 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____6916 -> None in
                                  let uu____6917 = maybe_extract_fv head2 in
                                  match uu____6917 with
                                  | Some x when
                                      let uu____6923 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____6923
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____6927 =
                                          maybe_extract_fv head3 in
                                        match uu____6927 with
                                        | Some uu____6930 -> Some true
                                        | uu____6931 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____6934 -> (head2, None) in
                                ((let is_arg_impure uu____6945 =
                                    match uu____6945 with
                                    | (e,q) ->
                                        let uu____6950 =
                                          let uu____6951 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____6951.FStar_Syntax_Syntax.n in
                                        (match uu____6950 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____6966 -> false) in
                                  let uu____6967 =
                                    let uu____6968 =
                                      let uu____6972 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____6972 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____6968 in
                                  if uu____6967
                                  then
                                    let uu____6975 =
                                      let uu____6976 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____6976 in
                                    failwith uu____6975
                                  else ());
                                 (let uu____6978 =
                                    maybe_unfold_action head_app in
                                  match uu____6978 with
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
                                      let uu____7013 = FStar_List.tl stack1 in
                                      norm cfg env uu____7013 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____7027 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____7027 in
                           let uu____7028 = FStar_List.tl stack1 in
                           norm cfg env uu____7028 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____7111  ->
                                     match uu____7111 with
                                     | (pat,wopt,tm) ->
                                         let uu____7149 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____7149))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____7175 = FStar_List.tl stack1 in
                           norm cfg env uu____7175 tm
                       | uu____7176 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____7185;
                             FStar_Syntax_Syntax.pos = uu____7186;
                             FStar_Syntax_Syntax.vars = uu____7187;_},uu____7188,uu____7189))::uu____7190
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7196 -> false in
                    if should_reify
                    then
                      let uu____7197 = FStar_List.tl stack1 in
                      let uu____7198 =
                        let uu____7199 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____7199 in
                      norm cfg env uu____7197 uu____7198
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____7202 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____7202
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___181_7208 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___181_7208.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___181_7208.primitive_steps)
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
                | uu____7210 ->
                    (match stack1 with
                     | uu____7211::uu____7212 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____7216)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____7231 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____7241 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____7241
                           | uu____7248 -> m in
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
              let uu____7260 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____7260 with
              | (uu____7261,return_repr) ->
                  let return_inst =
                    let uu____7268 =
                      let uu____7269 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____7269.FStar_Syntax_Syntax.n in
                    match uu____7268 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____7275::[])
                        ->
                        let uu____7281 =
                          let uu____7284 =
                            let uu____7285 =
                              let uu____7290 =
                                let uu____7292 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____7292] in
                              (return_tm, uu____7290) in
                            FStar_Syntax_Syntax.Tm_uinst uu____7285 in
                          FStar_Syntax_Syntax.mk uu____7284 in
                        uu____7281 None e.FStar_Syntax_Syntax.pos
                    | uu____7304 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____7307 =
                    let uu____7310 =
                      let uu____7311 =
                        let uu____7321 =
                          let uu____7323 = FStar_Syntax_Syntax.as_arg t in
                          let uu____7324 =
                            let uu____7326 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7326] in
                          uu____7323 :: uu____7324 in
                        (return_inst, uu____7321) in
                      FStar_Syntax_Syntax.Tm_app uu____7311 in
                    FStar_Syntax_Syntax.mk uu____7310 in
                  uu____7307 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____7339 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____7339 with
               | None  ->
                   let uu____7341 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____7341
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7342;
                     FStar_TypeChecker_Env.mtarget = uu____7343;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7344;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7355;
                     FStar_TypeChecker_Env.mtarget = uu____7356;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7357;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____7375 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____7375)
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
                (fun uu____7405  ->
                   match uu____7405 with
                   | (a,imp) ->
                       let uu____7412 = norm cfg env [] a in
                       (uu____7412, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___182_7427 = comp1 in
            let uu____7430 =
              let uu____7431 =
                let uu____7437 = norm cfg env [] t in
                let uu____7438 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7437, uu____7438) in
              FStar_Syntax_Syntax.Total uu____7431 in
            {
              FStar_Syntax_Syntax.n = uu____7430;
              FStar_Syntax_Syntax.tk = (uu___182_7427.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___182_7427.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___182_7427.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___183_7453 = comp1 in
            let uu____7456 =
              let uu____7457 =
                let uu____7463 = norm cfg env [] t in
                let uu____7464 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7463, uu____7464) in
              FStar_Syntax_Syntax.GTotal uu____7457 in
            {
              FStar_Syntax_Syntax.n = uu____7456;
              FStar_Syntax_Syntax.tk = (uu___183_7453.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_7453.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_7453.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7495  ->
                      match uu____7495 with
                      | (a,i) ->
                          let uu____7502 = norm cfg env [] a in
                          (uu____7502, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___146_7507  ->
                      match uu___146_7507 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____7511 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____7511
                      | f -> f)) in
            let uu___184_7515 = comp1 in
            let uu____7518 =
              let uu____7519 =
                let uu___185_7520 = ct in
                let uu____7521 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____7522 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____7525 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____7521;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___185_7520.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____7522;
                  FStar_Syntax_Syntax.effect_args = uu____7525;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____7519 in
            {
              FStar_Syntax_Syntax.n = uu____7518;
              FStar_Syntax_Syntax.tk = (uu___184_7515.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___184_7515.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___184_7515.FStar_Syntax_Syntax.vars)
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
            (let uu___186_7542 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___186_7542.tcenv);
               delta_level = (uu___186_7542.delta_level);
               primitive_steps = (uu___186_7542.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____7547 = norm1 t in
          FStar_Syntax_Util.non_informative uu____7547 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____7550 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___187_7564 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___187_7564.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___187_7564.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___187_7564.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____7574 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____7574
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___188_7579 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___188_7579.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___188_7579.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___188_7579.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___188_7579.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___189_7581 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___189_7581.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___189_7581.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___189_7581.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___189_7581.FStar_Syntax_Syntax.flags)
                    } in
              let uu___190_7582 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___190_7582.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___190_7582.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___190_7582.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____7588 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____7591  ->
        match uu____7591 with
        | (x,imp) ->
            let uu____7594 =
              let uu___191_7595 = x in
              let uu____7596 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___191_7595.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___191_7595.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____7596
              } in
            (uu____7594, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____7602 =
          FStar_List.fold_left
            (fun uu____7609  ->
               fun b  ->
                 match uu____7609 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____7602 with | (nbs,uu____7626) -> FStar_List.rev nbs
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
            let uu____7643 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____7643
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____7648 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____7648
               then
                 let uu____7652 =
                   let uu____7655 =
                     let uu____7656 =
                       let uu____7659 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____7659 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____7656 in
                   FStar_Util.Inl uu____7655 in
                 Some uu____7652
               else
                 (let uu____7663 =
                    let uu____7666 =
                      let uu____7667 =
                        let uu____7670 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____7670 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____7667 in
                    FStar_Util.Inl uu____7666 in
                  Some uu____7663))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____7683 -> lopt
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
              ((let uu____7695 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____7695
                then
                  let uu____7696 = FStar_Syntax_Print.term_to_string tm in
                  let uu____7697 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____7696
                    uu____7697
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___192_7708 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___192_7708.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7728  ->
                    let uu____7729 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7729);
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
              let uu____7766 =
                let uu___193_7767 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___193_7767.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___193_7767.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___193_7767.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____7766
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____7789),aq,r))::stack2 ->
              (log cfg
                 (fun uu____7805  ->
                    let uu____7806 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7806);
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
                 (let uu____7817 = FStar_ST.read m in
                  match uu____7817 with
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
                  | Some (uu____7843,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____7865 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____7865
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____7872  ->
                    let uu____7873 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7873);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7878 =
                  log cfg
                    (fun uu____7880  ->
                       let uu____7881 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____7882 =
                         let uu____7883 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____7890  ->
                                   match uu____7890 with
                                   | (p,uu____7896,uu____7897) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____7883
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____7881 uu____7882);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___147_7907  ->
                               match uu___147_7907 with
                               | FStar_TypeChecker_Env.Inlining 
                                 |FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____7908 -> false)) in
                     let steps' =
                       let uu____7911 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____7911
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___194_7914 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___194_7914.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___194_7914.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____7948 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____7968 = norm_pat env2 hd1 in
                         (match uu____7968 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____8004 = norm_pat env2 p1 in
                                        Prims.fst uu____8004)) in
                              ((let uu___195_8016 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___195_8016.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___195_8016.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____8033 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____8067  ->
                                   fun uu____8068  ->
                                     match (uu____8067, uu____8068) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____8133 = norm_pat env3 p1 in
                                         (match uu____8133 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____8033 with
                          | (pats1,env3) ->
                              ((let uu___196_8199 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___196_8199.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___196_8199.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___197_8213 = x in
                           let uu____8214 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___197_8213.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___197_8213.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8214
                           } in
                         ((let uu___198_8220 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___198_8220.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___198_8220.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___199_8225 = x in
                           let uu____8226 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___199_8225.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___199_8225.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8226
                           } in
                         ((let uu___200_8232 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___200_8232.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___200_8232.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___201_8242 = x in
                           let uu____8243 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___201_8242.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___201_8242.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8243
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___202_8250 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___202_8250.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___202_8250.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____8254 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____8257 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____8257 with
                                 | (p,wopt,e) ->
                                     let uu____8275 = norm_pat env1 p in
                                     (match uu____8275 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____8299 =
                                                  norm_or_whnf env2 w in
                                                Some uu____8299 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____8304 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____8304) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____8314) -> is_cons h
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
                  | uu____8325 -> false in
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
                  let uu____8424 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____8424 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____8481 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____8512 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____8524 ->
                                let uu____8525 =
                                  let uu____8526 = is_cons head1 in
                                  Prims.op_Negation uu____8526 in
                                FStar_Util.Inr uu____8525)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____8540 =
                             let uu____8541 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____8541.FStar_Syntax_Syntax.n in
                           (match uu____8540 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____8548 ->
                                let uu____8549 =
                                  let uu____8550 = is_cons head1 in
                                  Prims.op_Negation uu____8550 in
                                FStar_Util.Inr uu____8549))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____8584)::rest_a,(p1,uu____8587)::rest_p) ->
                      let uu____8615 = matches_pat t1 p1 in
                      (match uu____8615 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____8629 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____8700 = matches_pat scrutinee1 p1 in
                      (match uu____8700 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____8710  ->
                                 let uu____8711 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____8712 =
                                   let uu____8713 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____8713
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____8711 uu____8712);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____8722 =
                                        let uu____8723 =
                                          let uu____8733 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____8733, false) in
                                        Clos uu____8723 in
                                      uu____8722 :: env2) env1 s in
                             let uu____8756 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____8756))) in
                let uu____8757 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____8757
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___148_8771  ->
                match uu___148_8771 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____8774 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8778 -> d in
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
            let uu___203_8798 = config s e in
            {
              steps = (uu___203_8798.steps);
              tcenv = (uu___203_8798.tcenv);
              delta_level = (uu___203_8798.delta_level);
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
      fun t  -> let uu____8817 = config s e in norm_comp uu____8817 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8824 = config [] env in norm_universe uu____8824 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8831 = config [] env in ghost_to_pure_aux uu____8831 [] c
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
        let uu____8843 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8843 in
      let uu____8844 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____8844
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___204_8846 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___204_8846.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___204_8846.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____8847  ->
                    let uu____8848 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____8848))
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
            ((let uu____8861 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____8861);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____8870 = config [AllowUnboundUniverses] env in
          norm_comp uu____8870 [] c
        with
        | e ->
            ((let uu____8874 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____8874);
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
                   let uu____8911 =
                     let uu____8912 =
                       let uu____8917 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____8917) in
                     FStar_Syntax_Syntax.Tm_refine uu____8912 in
                   mk uu____8911 t01.FStar_Syntax_Syntax.pos
               | uu____8922 -> t2)
          | uu____8923 -> t2 in
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
        let uu____8939 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____8939 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____8955 ->
                 let uu____8959 = FStar_Syntax_Util.abs_formals e in
                 (match uu____8959 with
                  | (actuals,uu____8970,uu____8971) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____8993 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____8993 with
                         | (binders,args) ->
                             let uu____9003 =
                               (FStar_Syntax_Syntax.mk_Tm_app e args) None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____9008 =
                               let uu____9015 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_34  -> FStar_Util.Inl _0_34) in
                               FStar_All.pipe_right uu____9015
                                 (fun _0_35  -> Some _0_35) in
                             FStar_Syntax_Util.abs binders uu____9003
                               uu____9008)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____9051 =
        let uu____9055 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____9055, (t.FStar_Syntax_Syntax.n)) in
      match uu____9051 with
      | (Some sort,uu____9062) ->
          let uu____9064 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____9064
      | (uu____9065,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____9069 ->
          let uu____9073 = FStar_Syntax_Util.head_and_args t in
          (match uu____9073 with
           | (head1,args) ->
               let uu____9099 =
                 let uu____9100 = FStar_Syntax_Subst.compress head1 in
                 uu____9100.FStar_Syntax_Syntax.n in
               (match uu____9099 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____9103,thead) ->
                    let uu____9117 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____9117 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____9148 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___209_9152 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___209_9152.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___209_9152.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___209_9152.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___209_9152.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___209_9152.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___209_9152.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___209_9152.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___209_9152.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___209_9152.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___209_9152.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___209_9152.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___209_9152.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___209_9152.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___209_9152.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___209_9152.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___209_9152.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___209_9152.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___209_9152.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___209_9152.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___209_9152.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___209_9152.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___209_9152.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____9148 with
                            | (uu____9153,ty,uu____9155) ->
                                eta_expand_with_type env t ty))
                | uu____9156 ->
                    let uu____9157 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___210_9161 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___210_9161.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___210_9161.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___210_9161.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___210_9161.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___210_9161.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___210_9161.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___210_9161.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___210_9161.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___210_9161.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___210_9161.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___210_9161.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___210_9161.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___210_9161.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___210_9161.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___210_9161.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___210_9161.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___210_9161.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___210_9161.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___210_9161.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___210_9161.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___210_9161.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___210_9161.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____9157 with
                     | (uu____9162,ty,uu____9164) ->
                         eta_expand_with_type env t ty)))