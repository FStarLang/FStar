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
let is_empty uu___137_752 =
  match uu___137_752 with | [] -> true | uu____754 -> false
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
                    let uu___150_1577 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1577.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1577.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1577.FStar_Syntax_Syntax.lbeff);
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
                    let uu___151_1620 = lb in
                    let uu____1621 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1624 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1620.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1620.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1621;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1620.FStar_Syntax_Syntax.lbeff);
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
                                   ((let uu___152_1804 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_1804.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_1804.FStar_Syntax_Syntax.p)
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
                                   ((let uu___153_1987 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___153_1987.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___153_1987.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___154_2001 = x in
                                let uu____2002 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___154_2001.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___154_2001.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2002
                                } in
                              ((let uu___155_2008 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___155_2008.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___155_2008.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___156_2013 = x in
                                let uu____2014 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_2013.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_2013.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2014
                                } in
                              ((let uu___157_2020 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___157_2020.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_2020.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___158_2030 = x in
                                let uu____2031 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___158_2030.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___158_2030.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2031
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___159_2038 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___159_2038.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___159_2038.FStar_Syntax_Syntax.p)
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
                          let uu___160_2262 = b in
                          let uu____2263 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___160_2262.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___160_2262.FStar_Syntax_Syntax.index);
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
                        (fun uu___138_2350  ->
                           match uu___138_2350 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2354 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2354
                           | f -> f)) in
                 let uu____2358 =
                   let uu___161_2359 = c1 in
                   let uu____2360 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2360;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___161_2359.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___139_2364  ->
            match uu___139_2364 with
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
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3125 = arg_as_string a1 in
        (match uu____3125 with
         | Some s1 ->
             let uu____3129 = arg_as_list arg_as_string a2 in
             (match uu____3129 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3137 = string_as_const rng r in Some uu____3137
              | uu____3138 -> None)
         | uu____3141 -> None)
    | uu____3143 -> None in
  let string_of_int1 rng i =
    let uu____3154 = FStar_Util.string_of_int i in
    string_as_const rng uu____3154 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3170 = FStar_Util.string_of_int i in
    string_as_const rng uu____3170 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
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
                              let uu____3319 =
                                let uu____3329 =
                                  let uu____3339 =
                                    let uu____3349 =
                                      let uu____3359 =
                                        let uu____3368 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3368, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3374 =
                                        let uu____3384 =
                                          let uu____3393 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3393, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3400 =
                                          let uu____3410 =
                                            let uu____3422 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3422,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3410] in
                                        uu____3384 :: uu____3400 in
                                      uu____3359 :: uu____3374 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3349 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3339 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3329 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3319 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3309 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3299 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3289 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3279 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3269 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3259 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3249 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3239 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3229 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3219 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3209 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3199 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3189 in
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
      let uu____3746 =
        let uu____3747 =
          let uu____3748 = FStar_Syntax_Syntax.as_arg c in [uu____3748] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3747 in
      uu____3746 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3772 =
              let uu____3781 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3781, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3790  ->
                        fun uu____3791  ->
                          match (uu____3790, uu____3791) with
                          | ((int_to_t1,x),(uu____3802,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3808 =
              let uu____3818 =
                let uu____3827 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3827, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3836  ->
                          fun uu____3837  ->
                            match (uu____3836, uu____3837) with
                            | ((int_to_t1,x),(uu____3848,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3854 =
                let uu____3864 =
                  let uu____3873 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3873, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3882  ->
                            fun uu____3883  ->
                              match (uu____3882, uu____3883) with
                              | ((int_to_t1,x),(uu____3894,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3864] in
              uu____3818 :: uu____3854 in
            uu____3772 :: uu____3808)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3960)::(a1,uu____3962)::(a2,uu____3964)::[] ->
        let uu____3993 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3993 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3995 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3995
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4000 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____4000
         | uu____4005 -> None)
    | uu____4006 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,_)::(a1,_)::(a2,_)::[]|(_typ,_)::_::(a1,_)::(a2,_)::[] ->
        let uu____4088 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4088 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___162_4092 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4092.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4092.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4092.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___163_4099 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___163_4099.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___163_4099.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___163_4099.FStar_Syntax_Syntax.vars)
                })
         | uu____4104 -> None)
    | uu____4105 -> failwith "Unexpected number of arguments" in
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
      let uu____4116 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4116
      then tm
      else
        (let uu____4118 = FStar_Syntax_Util.head_and_args tm in
         match uu____4118 with
         | (head1,args) ->
             let uu____4144 =
               let uu____4145 = FStar_Syntax_Util.un_uinst head1 in
               uu____4145.FStar_Syntax_Syntax.n in
             (match uu____4144 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4149 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4149 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4161 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4161 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4164 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___164_4171 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___164_4171.tcenv);
           delta_level = (uu___164_4171.delta_level);
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
        let uu___165_4193 = t in
        {
          FStar_Syntax_Syntax.n = (uu___165_4193.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___165_4193.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___165_4193.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4212 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____4239 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4239
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
             let uu____4279 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4279
             then
               let uu____4280 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4280 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4446 -> tm)
             else
               (let uu____4456 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4456
                then
                  let uu____4457 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4457 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____4623 -> tm
                else
                  (let uu____4633 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4633
                   then
                     let uu____4634 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4634 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4723)::(uu____4724,(arg,uu____4726))::[]
                         -> arg
                     | uu____4767 -> tm
                   else
                     (let uu____4777 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4777
                      then
                        let uu____4778 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4778 with
                        | (Some (true ),uu____4811)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4835)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4859 -> tm
                      else
                        (let uu____4869 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4869
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
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
                              | (t,_)::[]
                                |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                                (t,_)::[] ->
                                  let uu____4993 =
                                    let uu____4994 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4994.FStar_Syntax_Syntax.n in
                                  (match uu____4993 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4997::[],body,uu____4999) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5025 -> tm)
                                   | uu____5027 -> tm)
                              | uu____5028 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5035 -> tm)
let is_norm_request hd1 args =
  let uu____5050 =
    let uu____5054 =
      let uu____5055 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5055.FStar_Syntax_Syntax.n in
    (uu____5054, args) in
  match uu____5050 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5060::uu____5061::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5064::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____5066 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____5099 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_5106  ->
    match uu___140_5106 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____5108;
           FStar_Syntax_Syntax.pos = uu____5109;
           FStar_Syntax_Syntax.vars = uu____5110;_},uu____5111,uu____5112))::uu____5113
        -> true
    | uu____5119 -> false
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
            (fun uu____5234  ->
               let uu____5235 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____5236 = FStar_Syntax_Print.term_to_string t1 in
               let uu____5237 =
                 let uu____5238 =
                   let uu____5240 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____5240 in
                 stack_to_string uu____5238 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____5235
                 uu____5236 uu____5237);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____5252 ->
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
                 let uu___166_5309 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___166_5309.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___166_5309.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___166_5309.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____5335 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____5335) && (is_norm_request hd1 args))
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
                 let uu___167_5348 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___167_5348.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___167_5348.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____5353;
                  FStar_Syntax_Syntax.pos = uu____5354;
                  FStar_Syntax_Syntax.vars = uu____5355;_},a1::a2::rest)
               ->
               let uu____5389 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5389 with
                | (hd1,uu____5400) ->
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
                    (FStar_Const.Const_reflect uu____5455);
                  FStar_Syntax_Syntax.tk = uu____5456;
                  FStar_Syntax_Syntax.pos = uu____5457;
                  FStar_Syntax_Syntax.vars = uu____5458;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____5481 = FStar_List.tl stack1 in
               norm cfg env uu____5481 (Prims.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____5484;
                  FStar_Syntax_Syntax.pos = uu____5485;
                  FStar_Syntax_Syntax.vars = uu____5486;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____5509 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5509 with
                | (reify_head,uu____5520) ->
                    let a1 =
                      let uu____5536 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____5536 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____5539);
                            FStar_Syntax_Syntax.tk = uu____5540;
                            FStar_Syntax_Syntax.pos = uu____5541;
                            FStar_Syntax_Syntax.vars = uu____5542;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____5567 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____5575 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____5575
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____5582 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____5582
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____5585 =
                      let uu____5589 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____5589, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____5585 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_5598  ->
                         match uu___141_5598 with
                         | FStar_TypeChecker_Env.UnfoldTac 
                           |FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____5601 =
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
                 if uu____5601 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____5605 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____5605 in
                  let uu____5606 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____5606 with
                  | None  ->
                      (log cfg
                         (fun uu____5617  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____5623  ->
                            let uu____5624 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____5625 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____5624 uu____5625);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____5632))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____5645 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____5646 ->
                              let uu____5647 =
                                let uu____5648 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____5648 in
                              failwith uu____5647
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____5655 = lookup_bvar env x in
               (match uu____5655 with
                | Univ uu____5656 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____5671 = FStar_ST.read r in
                      (match uu____5671 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____5690  ->
                                 let uu____5691 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____5692 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____5691
                                   uu____5692);
                            (let uu____5693 =
                               let uu____5694 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____5694.FStar_Syntax_Syntax.n in
                             match uu____5693 with
                             | FStar_Syntax_Syntax.Tm_abs uu____5697 ->
                                 norm cfg env2 stack1 t'
                             | uu____5712 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____5745)::uu____5746 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____5751)::uu____5752 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____5758,uu____5759))::stack_rest ->
                    (match c with
                     | Univ uu____5762 -> norm cfg (c :: env) stack_rest t1
                     | uu____5763 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____5766::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____5779  ->
                                         let uu____5780 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5780);
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
                                           (fun uu___142_5794  ->
                                              match uu___142_5794 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____5795 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____5797  ->
                                         let uu____5798 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5798);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____5809  ->
                                         let uu____5810 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5810);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____5811 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____5818 ->
                                   let cfg1 =
                                     let uu___168_5826 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___168_5826.tcenv);
                                       delta_level =
                                         (uu___168_5826.delta_level);
                                       primitive_steps =
                                         (uu___168_5826.primitive_steps)
                                     } in
                                   let uu____5827 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____5827)
                          | uu____5828::tl1 ->
                              (log cfg
                                 (fun uu____5838  ->
                                    let uu____5839 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____5839);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___169_5863 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___169_5863.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____5876  ->
                          let uu____5877 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5877);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____5888 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5888
                    else
                      (let uu____5890 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____5890 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____5919 =
                                   let uu____5925 =
                                     let uu____5926 =
                                       let uu____5927 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____5927 in
                                     FStar_All.pipe_right uu____5926
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____5925
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____5919
                                   (fun _0_32  -> Some _0_32)
                             | uu____5952 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5966  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5971  ->
                                 let uu____5972 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5972);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___170_5982 = cfg in
                               let uu____5983 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___170_5982.steps);
                                 tcenv = (uu___170_5982.tcenv);
                                 delta_level = (uu___170_5982.delta_level);
                                 primitive_steps = uu____5983
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
                      (fun uu____6015  ->
                         fun stack2  ->
                           match uu____6015 with
                           | (a,aq) ->
                               let uu____6023 =
                                 let uu____6024 =
                                   let uu____6028 =
                                     let uu____6029 =
                                       let uu____6039 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____6039, false) in
                                     Clos uu____6029 in
                                   (uu____6028, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____6024 in
                               uu____6023 :: stack2) args) in
               (log cfg
                  (fun uu____6061  ->
                     let uu____6062 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____6062);
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
                             ((let uu___171_6083 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___171_6083.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___171_6083.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____6084 ->
                      let uu____6087 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6087)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____6090 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____6090 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____6106 =
                          let uu____6107 =
                            let uu____6112 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___172_6113 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___172_6113.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___172_6113.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____6112) in
                          FStar_Syntax_Syntax.Tm_refine uu____6107 in
                        mk uu____6106 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____6126 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____6126
               else
                 (let uu____6128 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____6128 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____6134 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____6140  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____6134 c1 in
                      let t2 =
                        let uu____6147 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____6147 c2 in
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
                | uu____6204 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____6207  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____6220 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____6220
                        | FStar_Util.Inr c ->
                            let uu____6228 = norm_comp cfg env c in
                            FStar_Util.Inr uu____6228 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____6233 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____6233)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____6284,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____6285;
                              FStar_Syntax_Syntax.lbunivs = uu____6286;
                              FStar_Syntax_Syntax.lbtyp = uu____6287;
                              FStar_Syntax_Syntax.lbeff = uu____6288;
                              FStar_Syntax_Syntax.lbdef = uu____6289;_}::uu____6290),uu____6291)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____6317 =
                 (let uu____6318 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____6318) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____6319 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____6319))) in
               if uu____6317
               then
                 let env1 =
                   let uu____6322 =
                     let uu____6323 =
                       let uu____6333 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____6333,
                         false) in
                     Clos uu____6323 in
                   uu____6322 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____6357 =
                    let uu____6360 =
                      let uu____6361 =
                        let uu____6362 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____6362
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____6361] in
                    FStar_Syntax_Subst.open_term uu____6360 body in
                  match uu____6357 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___173_6368 = lb in
                        let uu____6369 =
                          let uu____6372 =
                            let uu____6373 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____6373 Prims.fst in
                          FStar_All.pipe_right uu____6372
                            (fun _0_33  -> FStar_Util.Inl _0_33) in
                        let uu____6382 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____6385 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____6369;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___173_6368.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6382;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___173_6368.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6385
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____6395  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____6411 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____6411
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____6424 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____6446  ->
                        match uu____6446 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____6485 =
                                let uu___174_6486 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___174_6486.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___174_6486.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____6485 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____6424 with
                | (rec_env,memos,uu____6546) ->
                    let uu____6561 =
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
                             let uu____6603 =
                               let uu____6604 =
                                 let uu____6614 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____6614, false) in
                               Clos uu____6604 in
                             uu____6603 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____6652;
                             FStar_Syntax_Syntax.pos = uu____6653;
                             FStar_Syntax_Syntax.vars = uu____6654;_},uu____6655,uu____6656))::uu____6657
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6663 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____6670 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____6670
                        then
                          let uu___175_6671 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___175_6671.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___175_6671.primitive_steps)
                          }
                        else
                          (let uu___176_6673 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___176_6673.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___176_6673.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____6675 =
                         let uu____6676 = FStar_Syntax_Subst.compress head1 in
                         uu____6676.FStar_Syntax_Syntax.n in
                       match uu____6675 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6690 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6690 with
                            | (uu____6691,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____6695 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____6702 =
                                         let uu____6703 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____6703.FStar_Syntax_Syntax.n in
                                       match uu____6702 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____6708,uu____6709))
                                           ->
                                           let uu____6718 =
                                             let uu____6719 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____6719.FStar_Syntax_Syntax.n in
                                           (match uu____6718 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____6724,msrc,uu____6726))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____6735 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____6735
                                            | uu____6736 -> None)
                                       | uu____6737 -> None in
                                     let uu____6738 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____6738 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___177_6742 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___177_6742.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___177_6742.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___177_6742.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____6743 =
                                            FStar_List.tl stack1 in
                                          let uu____6744 =
                                            let uu____6745 =
                                              let uu____6748 =
                                                let uu____6749 =
                                                  let uu____6757 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____6757) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____6749 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6748 in
                                            uu____6745 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____6743 uu____6744
                                      | None  ->
                                          let uu____6774 =
                                            let uu____6775 = is_return body in
                                            match uu____6775 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6778;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6779;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6780;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____6785 -> false in
                                          if uu____6774
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
                                               let uu____6805 =
                                                 let uu____6808 =
                                                   let uu____6809 =
                                                     let uu____6824 =
                                                       let uu____6826 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6826] in
                                                     (uu____6824, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____6809 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6808 in
                                               uu____6805 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____6859 =
                                                 let uu____6860 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____6860.FStar_Syntax_Syntax.n in
                                               match uu____6859 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____6866::uu____6867::[])
                                                   ->
                                                   let uu____6873 =
                                                     let uu____6876 =
                                                       let uu____6877 =
                                                         let uu____6882 =
                                                           let uu____6884 =
                                                             let uu____6885 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____6885 in
                                                           let uu____6886 =
                                                             let uu____6888 =
                                                               let uu____6889
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____6889 in
                                                             [uu____6888] in
                                                           uu____6884 ::
                                                             uu____6886 in
                                                         (bind1, uu____6882) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____6877 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6876 in
                                                   uu____6873 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____6901 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____6907 =
                                                 let uu____6910 =
                                                   let uu____6911 =
                                                     let uu____6921 =
                                                       let uu____6923 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____6924 =
                                                         let uu____6926 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____6927 =
                                                           let uu____6929 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____6930 =
                                                             let uu____6932 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____6933 =
                                                               let uu____6935
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____6936
                                                                 =
                                                                 let uu____6938
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____6938] in
                                                               uu____6935 ::
                                                                 uu____6936 in
                                                             uu____6932 ::
                                                               uu____6933 in
                                                           uu____6929 ::
                                                             uu____6930 in
                                                         uu____6926 ::
                                                           uu____6927 in
                                                       uu____6923 ::
                                                         uu____6924 in
                                                     (bind_inst, uu____6921) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6911 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6910 in
                                               uu____6907 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____6950 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____6950 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6968 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6968 with
                            | (uu____6969,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6992 =
                                        let uu____6993 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6993.FStar_Syntax_Syntax.n in
                                      match uu____6992 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6999) -> t4
                                      | uu____7004 -> head2 in
                                    let uu____7005 =
                                      let uu____7006 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____7006.FStar_Syntax_Syntax.n in
                                    match uu____7005 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____7011 -> None in
                                  let uu____7012 = maybe_extract_fv head2 in
                                  match uu____7012 with
                                  | Some x when
                                      let uu____7018 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____7018
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____7022 =
                                          maybe_extract_fv head3 in
                                        match uu____7022 with
                                        | Some uu____7025 -> Some true
                                        | uu____7026 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____7029 -> (head2, None) in
                                ((let is_arg_impure uu____7040 =
                                    match uu____7040 with
                                    | (e,q) ->
                                        let uu____7045 =
                                          let uu____7046 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____7046.FStar_Syntax_Syntax.n in
                                        (match uu____7045 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____7061 -> false) in
                                  let uu____7062 =
                                    let uu____7063 =
                                      let uu____7067 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____7067 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____7063 in
                                  if uu____7062
                                  then
                                    let uu____7070 =
                                      let uu____7071 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____7071 in
                                    failwith uu____7070
                                  else ());
                                 (let uu____7073 =
                                    maybe_unfold_action head_app in
                                  match uu____7073 with
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
                                      let uu____7108 = FStar_List.tl stack1 in
                                      norm cfg env uu____7108 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____7122 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____7122 in
                           let uu____7123 = FStar_List.tl stack1 in
                           norm cfg env uu____7123 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____7206  ->
                                     match uu____7206 with
                                     | (pat,wopt,tm) ->
                                         let uu____7244 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____7244))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____7270 = FStar_List.tl stack1 in
                           norm cfg env uu____7270 tm
                       | uu____7271 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____7280;
                             FStar_Syntax_Syntax.pos = uu____7281;
                             FStar_Syntax_Syntax.vars = uu____7282;_},uu____7283,uu____7284))::uu____7285
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7291 -> false in
                    if should_reify
                    then
                      let uu____7292 = FStar_List.tl stack1 in
                      let uu____7293 =
                        let uu____7294 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____7294 in
                      norm cfg env uu____7292 uu____7293
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____7297 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____7297
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___178_7303 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___178_7303.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___178_7303.primitive_steps)
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
                | uu____7305 ->
                    (match stack1 with
                     | uu____7306::uu____7307 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____7311)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____7326 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____7336 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____7336
                           | uu____7343 -> m in
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
              let uu____7355 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____7355 with
              | (uu____7356,return_repr) ->
                  let return_inst =
                    let uu____7363 =
                      let uu____7364 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____7364.FStar_Syntax_Syntax.n in
                    match uu____7363 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____7370::[])
                        ->
                        let uu____7376 =
                          let uu____7379 =
                            let uu____7380 =
                              let uu____7385 =
                                let uu____7387 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____7387] in
                              (return_tm, uu____7385) in
                            FStar_Syntax_Syntax.Tm_uinst uu____7380 in
                          FStar_Syntax_Syntax.mk uu____7379 in
                        uu____7376 None e.FStar_Syntax_Syntax.pos
                    | uu____7399 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____7402 =
                    let uu____7405 =
                      let uu____7406 =
                        let uu____7416 =
                          let uu____7418 = FStar_Syntax_Syntax.as_arg t in
                          let uu____7419 =
                            let uu____7421 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7421] in
                          uu____7418 :: uu____7419 in
                        (return_inst, uu____7416) in
                      FStar_Syntax_Syntax.Tm_app uu____7406 in
                    FStar_Syntax_Syntax.mk uu____7405 in
                  uu____7402 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____7434 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____7434 with
               | None  ->
                   let uu____7436 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____7436
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7437;
                     FStar_TypeChecker_Env.mtarget = uu____7438;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7439;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7450;
                     FStar_TypeChecker_Env.mtarget = uu____7451;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7452;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____7470 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____7470)
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
                (fun uu____7500  ->
                   match uu____7500 with
                   | (a,imp) ->
                       let uu____7507 = norm cfg env [] a in
                       (uu____7507, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___179_7522 = comp1 in
            let uu____7525 =
              let uu____7526 =
                let uu____7532 = norm cfg env [] t in
                let uu____7533 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7532, uu____7533) in
              FStar_Syntax_Syntax.Total uu____7526 in
            {
              FStar_Syntax_Syntax.n = uu____7525;
              FStar_Syntax_Syntax.tk = (uu___179_7522.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_7522.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_7522.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___180_7548 = comp1 in
            let uu____7551 =
              let uu____7552 =
                let uu____7558 = norm cfg env [] t in
                let uu____7559 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7558, uu____7559) in
              FStar_Syntax_Syntax.GTotal uu____7552 in
            {
              FStar_Syntax_Syntax.n = uu____7551;
              FStar_Syntax_Syntax.tk = (uu___180_7548.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_7548.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_7548.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7590  ->
                      match uu____7590 with
                      | (a,i) ->
                          let uu____7597 = norm cfg env [] a in
                          (uu____7597, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_7602  ->
                      match uu___143_7602 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____7606 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____7606
                      | f -> f)) in
            let uu___181_7610 = comp1 in
            let uu____7613 =
              let uu____7614 =
                let uu___182_7615 = ct in
                let uu____7616 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____7617 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____7620 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____7616;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___182_7615.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____7617;
                  FStar_Syntax_Syntax.effect_args = uu____7620;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____7614 in
            {
              FStar_Syntax_Syntax.n = uu____7613;
              FStar_Syntax_Syntax.tk = (uu___181_7610.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___181_7610.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___181_7610.FStar_Syntax_Syntax.vars)
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
            (let uu___183_7637 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___183_7637.tcenv);
               delta_level = (uu___183_7637.delta_level);
               primitive_steps = (uu___183_7637.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____7642 = norm1 t in
          FStar_Syntax_Util.non_informative uu____7642 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____7645 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___184_7659 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___184_7659.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___184_7659.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___184_7659.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____7669 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____7669
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___185_7674 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_7674.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_7674.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_7674.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_7674.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___186_7676 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___186_7676.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___186_7676.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___186_7676.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___186_7676.FStar_Syntax_Syntax.flags)
                    } in
              let uu___187_7677 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___187_7677.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___187_7677.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___187_7677.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____7683 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____7686  ->
        match uu____7686 with
        | (x,imp) ->
            let uu____7689 =
              let uu___188_7690 = x in
              let uu____7691 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___188_7690.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___188_7690.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____7691
              } in
            (uu____7689, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____7697 =
          FStar_List.fold_left
            (fun uu____7704  ->
               fun b  ->
                 match uu____7704 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____7697 with | (nbs,uu____7721) -> FStar_List.rev nbs
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
            let uu____7738 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____7738
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____7743 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____7743
               then
                 let uu____7747 =
                   let uu____7750 =
                     let uu____7751 =
                       let uu____7754 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____7754 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____7751 in
                   FStar_Util.Inl uu____7750 in
                 Some uu____7747
               else
                 (let uu____7758 =
                    let uu____7761 =
                      let uu____7762 =
                        let uu____7765 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____7765 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____7762 in
                    FStar_Util.Inl uu____7761 in
                  Some uu____7758))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____7778 -> lopt
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
              ((let uu____7790 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____7790
                then
                  let uu____7791 = FStar_Syntax_Print.term_to_string tm in
                  let uu____7792 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____7791
                    uu____7792
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___189_7803 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___189_7803.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7823  ->
                    let uu____7824 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7824);
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
              let uu____7861 =
                let uu___190_7862 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___190_7862.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___190_7862.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___190_7862.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____7861
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____7884),aq,r))::stack2 ->
              (log cfg
                 (fun uu____7900  ->
                    let uu____7901 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7901);
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
                 (let uu____7912 = FStar_ST.read m in
                  match uu____7912 with
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
                  | Some (uu____7938,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____7960 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____7960
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____7967  ->
                    let uu____7968 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7968);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7973 =
                  log cfg
                    (fun uu____7975  ->
                       let uu____7976 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____7977 =
                         let uu____7978 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____7985  ->
                                   match uu____7985 with
                                   | (p,uu____7991,uu____7992) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____7978
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____7976 uu____7977);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_8002  ->
                               match uu___144_8002 with
                               | FStar_TypeChecker_Env.Inlining 
                                 |FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____8003 -> false)) in
                     let steps' =
                       let uu____8006 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____8006
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___191_8009 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___191_8009.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___191_8009.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____8043 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____8063 = norm_pat env2 hd1 in
                         (match uu____8063 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____8099 = norm_pat env2 p1 in
                                        Prims.fst uu____8099)) in
                              ((let uu___192_8111 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___192_8111.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___192_8111.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____8128 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____8162  ->
                                   fun uu____8163  ->
                                     match (uu____8162, uu____8163) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____8228 = norm_pat env3 p1 in
                                         (match uu____8228 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____8128 with
                          | (pats1,env3) ->
                              ((let uu___193_8294 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___193_8294.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___193_8294.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___194_8308 = x in
                           let uu____8309 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_8308.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_8308.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8309
                           } in
                         ((let uu___195_8315 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_8315.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_8315.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___196_8320 = x in
                           let uu____8321 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_8320.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_8320.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8321
                           } in
                         ((let uu___197_8327 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___197_8327.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_8327.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___198_8337 = x in
                           let uu____8338 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___198_8337.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___198_8337.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8338
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___199_8345 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___199_8345.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___199_8345.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____8349 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____8352 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____8352 with
                                 | (p,wopt,e) ->
                                     let uu____8370 = norm_pat env1 p in
                                     (match uu____8370 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____8394 =
                                                  norm_or_whnf env2 w in
                                                Some uu____8394 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____8399 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____8399) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____8409) -> is_cons h
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
                  | uu____8420 -> false in
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
                  let uu____8519 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____8519 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____8576 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____8607 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____8619 ->
                                let uu____8620 =
                                  let uu____8621 = is_cons head1 in
                                  Prims.op_Negation uu____8621 in
                                FStar_Util.Inr uu____8620)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____8635 =
                             let uu____8636 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____8636.FStar_Syntax_Syntax.n in
                           (match uu____8635 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____8643 ->
                                let uu____8644 =
                                  let uu____8645 = is_cons head1 in
                                  Prims.op_Negation uu____8645 in
                                FStar_Util.Inr uu____8644))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____8679)::rest_a,(p1,uu____8682)::rest_p) ->
                      let uu____8710 = matches_pat t1 p1 in
                      (match uu____8710 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____8724 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____8795 = matches_pat scrutinee1 p1 in
                      (match uu____8795 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____8805  ->
                                 let uu____8806 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____8807 =
                                   let uu____8808 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____8808
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____8806 uu____8807);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____8817 =
                                        let uu____8818 =
                                          let uu____8828 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____8828, false) in
                                        Clos uu____8818 in
                                      uu____8817 :: env2) env1 s in
                             let uu____8851 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____8851))) in
                let uu____8852 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____8852
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_8866  ->
                match uu___145_8866 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____8869 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8873 -> d in
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
            let uu___200_8893 = config s e in
            {
              steps = (uu___200_8893.steps);
              tcenv = (uu___200_8893.tcenv);
              delta_level = (uu___200_8893.delta_level);
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
      fun t  -> let uu____8912 = config s e in norm_comp uu____8912 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8919 = config [] env in norm_universe uu____8919 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8926 = config [] env in ghost_to_pure_aux uu____8926 [] c
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
        let uu____8938 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8938 in
      let uu____8939 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____8939
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___201_8941 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___201_8941.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___201_8941.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____8942  ->
                    let uu____8943 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____8943))
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
            ((let uu____8956 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____8956);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____8965 = config [AllowUnboundUniverses] env in
          norm_comp uu____8965 [] c
        with
        | e ->
            ((let uu____8969 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____8969);
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
                   let uu____9006 =
                     let uu____9007 =
                       let uu____9012 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____9012) in
                     FStar_Syntax_Syntax.Tm_refine uu____9007 in
                   mk uu____9006 t01.FStar_Syntax_Syntax.pos
               | uu____9017 -> t2)
          | uu____9018 -> t2 in
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
        let uu____9034 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____9034 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____9050 ->
                 let uu____9054 = FStar_Syntax_Util.abs_formals e in
                 (match uu____9054 with
                  | (actuals,uu____9065,uu____9066) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____9088 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____9088 with
                         | (binders,args) ->
                             let uu____9098 =
                               (FStar_Syntax_Syntax.mk_Tm_app e args) None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____9103 =
                               let uu____9110 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_34  -> FStar_Util.Inl _0_34) in
                               FStar_All.pipe_right uu____9110
                                 (fun _0_35  -> Some _0_35) in
                             FStar_Syntax_Util.abs binders uu____9098
                               uu____9103)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____9146 =
        let uu____9150 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____9150, (t.FStar_Syntax_Syntax.n)) in
      match uu____9146 with
      | (Some sort,uu____9157) ->
          let uu____9159 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____9159
      | (uu____9160,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____9164 ->
          let uu____9168 = FStar_Syntax_Util.head_and_args t in
          (match uu____9168 with
           | (head1,args) ->
               let uu____9194 =
                 let uu____9195 = FStar_Syntax_Subst.compress head1 in
                 uu____9195.FStar_Syntax_Syntax.n in
               (match uu____9194 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____9198,thead) ->
                    let uu____9212 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____9212 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____9243 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___206_9247 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___206_9247.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___206_9247.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___206_9247.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___206_9247.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___206_9247.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___206_9247.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___206_9247.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___206_9247.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___206_9247.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___206_9247.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___206_9247.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___206_9247.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___206_9247.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___206_9247.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___206_9247.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___206_9247.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___206_9247.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___206_9247.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___206_9247.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___206_9247.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___206_9247.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___206_9247.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____9243 with
                            | (uu____9248,ty,uu____9250) ->
                                eta_expand_with_type env t ty))
                | uu____9251 ->
                    let uu____9252 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___207_9256 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___207_9256.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___207_9256.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___207_9256.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___207_9256.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___207_9256.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___207_9256.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___207_9256.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___207_9256.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___207_9256.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___207_9256.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___207_9256.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___207_9256.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___207_9256.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___207_9256.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___207_9256.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___207_9256.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___207_9256.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___207_9256.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___207_9256.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___207_9256.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___207_9256.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___207_9256.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____9252 with
                     | (uu____9257,ty,uu____9259) ->
                         eta_expand_with_type env t ty)))