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
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____876 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____879 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____884 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____884 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____895 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____895 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____900 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____903 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____903 with
                                  | (uu____906,m) -> n1 <= m)) in
                        if uu____900 then rest1 else us1
                    | uu____910 -> us1)
               | uu____913 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____916 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____916 in
        let uu____918 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____918
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____920 = aux u in
           match uu____920 with
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
          (fun uu____1017  ->
             let uu____1018 = FStar_Syntax_Print.tag_of_term t in
             let uu____1019 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1018
               uu____1019);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1020 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1023 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1044 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1045 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1046 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1047 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1057 =
                    let uu____1058 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1058 in
                  mk uu____1057 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1065 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1065
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1067 = lookup_bvar env x in
                  (match uu____1067 with
                   | Univ uu____1068 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1072) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1140 = closures_as_binders_delayed cfg env bs in
                  (match uu____1140 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1160 =
                         let uu____1161 =
                           let uu____1176 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1176) in
                         FStar_Syntax_Syntax.Tm_abs uu____1161 in
                       mk uu____1160 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1206 = closures_as_binders_delayed cfg env bs in
                  (match uu____1206 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1237 =
                    let uu____1244 =
                      let uu____1248 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1248] in
                    closures_as_binders_delayed cfg env uu____1244 in
                  (match uu____1237 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1262 =
                         let uu____1263 =
                           let uu____1268 =
                             let uu____1269 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1269
                               FStar_Pervasives.fst in
                           (uu____1268, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1263 in
                       mk uu____1262 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1337 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1337
                    | FStar_Util.Inr c ->
                        let uu____1351 = close_comp cfg env c in
                        FStar_Util.Inr uu____1351 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1366 =
                    let uu____1367 =
                      let uu____1385 = closure_as_term_delayed cfg env t11 in
                      (uu____1385, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1367 in
                  mk uu____1366 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1423 =
                    let uu____1424 =
                      let uu____1429 = closure_as_term_delayed cfg env t' in
                      let uu____1432 =
                        let uu____1433 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1433 in
                      (uu____1429, uu____1432) in
                    FStar_Syntax_Syntax.Tm_meta uu____1424 in
                  mk uu____1423 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1475 =
                    let uu____1476 =
                      let uu____1481 = closure_as_term_delayed cfg env t' in
                      let uu____1484 =
                        let uu____1485 =
                          let uu____1490 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1490) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1485 in
                      (uu____1481, uu____1484) in
                    FStar_Syntax_Syntax.Tm_meta uu____1476 in
                  mk uu____1475 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1509 =
                    let uu____1510 =
                      let uu____1515 = closure_as_term_delayed cfg env t' in
                      let uu____1518 =
                        let uu____1519 =
                          let uu____1525 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1525) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1519 in
                      (uu____1515, uu____1518) in
                    FStar_Syntax_Syntax.Tm_meta uu____1510 in
                  mk uu____1509 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1538 =
                    let uu____1539 =
                      let uu____1544 = closure_as_term_delayed cfg env t' in
                      (uu____1544, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1539 in
                  mk uu____1538 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1565  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1576 -> body
                    | FStar_Util.Inl uu____1577 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___150_1579 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1579.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1579.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1579.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1586,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1610  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1615 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1615
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1619  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___151_1622 = lb in
                    let uu____1623 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1626 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1622.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1622.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1623;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1622.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1626
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1637  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1692 =
                    match uu____1692 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1738 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1754 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1788  ->
                                        fun uu____1789  ->
                                          match (uu____1788, uu____1789) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1854 =
                                                norm_pat env3 p1 in
                                              (match uu____1854 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1754 with
                               | (pats1,env3) ->
                                   ((let uu___152_1920 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_1920.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_1920.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___153_1934 = x in
                                let uu____1935 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_1934.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_1934.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1935
                                } in
                              ((let uu___154_1941 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_1941.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_1941.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___155_1946 = x in
                                let uu____1947 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_1946.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_1946.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1947
                                } in
                              ((let uu___156_1953 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_1953.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_1953.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___157_1963 = x in
                                let uu____1964 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_1963.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_1963.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1964
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___158_1971 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_1971.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_1971.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1974 = norm_pat env1 pat in
                        (match uu____1974 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1998 =
                                     closure_as_term cfg env2 w in
                                   Some uu____1998 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2003 =
                    let uu____2004 =
                      let uu____2020 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2020) in
                    FStar_Syntax_Syntax.Tm_match uu____2004 in
                  mk uu____2003 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2073 -> closure_as_term cfg env t
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
        | uu____2089 ->
            FStar_List.map
              (fun uu____2099  ->
                 match uu____2099 with
                 | (x,imp) ->
                     let uu____2114 = closure_as_term_delayed cfg env x in
                     (uu____2114, imp)) args
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
        let uu____2126 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2150  ->
                  fun uu____2151  ->
                    match (uu____2150, uu____2151) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___159_2195 = b in
                          let uu____2196 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___159_2195.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___159_2195.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2196
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2126 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2243 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2255 = closure_as_term_delayed cfg env t in
                 let uu____2256 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2255 uu____2256
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2266 = closure_as_term_delayed cfg env t in
                 let uu____2267 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2266 uu____2267
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
                        (fun uu___138_2283  ->
                           match uu___138_2283 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2287 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2287
                           | f -> f)) in
                 let uu____2291 =
                   let uu___160_2292 = c1 in
                   let uu____2293 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2293;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___160_2292.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2291)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___139_2297  ->
            match uu___139_2297 with
            | FStar_Syntax_Syntax.DECREASES uu____2298 -> false
            | uu____2301 -> true))
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
            let uu____2329 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2329
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2346 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2346
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2372 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2396 =
      let uu____2397 =
        let uu____2403 = FStar_Util.string_of_int i in (uu____2403, None) in
      FStar_Const.Const_int uu____2397 in
    const_as_tm uu____2396 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2430 =
    match uu____2430 with
    | (a,uu____2435) ->
        let uu____2437 =
          let uu____2438 = FStar_Syntax_Subst.compress a in
          uu____2438.FStar_Syntax_Syntax.n in
        (match uu____2437 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2448 = FStar_Util.int_of_string i in Some uu____2448
         | uu____2449 -> None) in
  let arg_as_bounded_int uu____2458 =
    match uu____2458 with
    | (a,uu____2465) ->
        let uu____2469 =
          let uu____2470 = FStar_Syntax_Subst.compress a in
          uu____2470.FStar_Syntax_Syntax.n in
        (match uu____2469 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2477;
                FStar_Syntax_Syntax.pos = uu____2478;
                FStar_Syntax_Syntax.vars = uu____2479;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2481;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2482;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2483;_},uu____2484)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2515 =
               let uu____2518 = FStar_Util.int_of_string i in
               (fv1, uu____2518) in
             Some uu____2515
         | uu____2521 -> None) in
  let arg_as_bool uu____2530 =
    match uu____2530 with
    | (a,uu____2535) ->
        let uu____2537 =
          let uu____2538 = FStar_Syntax_Subst.compress a in
          uu____2538.FStar_Syntax_Syntax.n in
        (match uu____2537 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2543 -> None) in
  let arg_as_char uu____2550 =
    match uu____2550 with
    | (a,uu____2555) ->
        let uu____2557 =
          let uu____2558 = FStar_Syntax_Subst.compress a in
          uu____2558.FStar_Syntax_Syntax.n in
        (match uu____2557 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2563 -> None) in
  let arg_as_string uu____2570 =
    match uu____2570 with
    | (a,uu____2575) ->
        let uu____2577 =
          let uu____2578 = FStar_Syntax_Subst.compress a in
          uu____2578.FStar_Syntax_Syntax.n in
        (match uu____2577 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2583)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2586 -> None) in
  let arg_as_list f uu____2607 =
    match uu____2607 with
    | (a,uu____2616) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2635 -> None
          | (Some x)::xs ->
              let uu____2645 = sequence xs in
              (match uu____2645 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2656 = FStar_Syntax_Util.list_elements a in
        (match uu____2656 with
         | None  -> None
         | Some elts ->
             let uu____2666 =
               FStar_List.map
                 (fun x  ->
                    let uu____2671 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2671) elts in
             sequence uu____2666) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2701 = f a in Some uu____2701
    | uu____2702 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2741 = f a0 a1 in Some uu____2741
    | uu____2742 -> None in
  let unary_op as_a f r args =
    let uu____2786 = FStar_List.map as_a args in lift_unary (f r) uu____2786 in
  let binary_op as_a f r args =
    let uu____2836 = FStar_List.map as_a args in lift_binary (f r) uu____2836 in
  let as_primitive_step uu____2853 =
    match uu____2853 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2891 = f x in int_as_const r uu____2891) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2914 = f x y in int_as_const r uu____2914) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2931 = f x in bool_as_const r uu____2931) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2954 = f x y in bool_as_const r uu____2954) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2977 = f x y in string_as_const r uu____2977) in
  let list_of_string' rng s =
    let name l =
      let uu____2991 =
        let uu____2992 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2992 in
      mk uu____2991 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3002 =
      let uu____3004 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3004 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3002 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3058 = arg_as_string a1 in
        (match uu____3058 with
         | Some s1 ->
             let uu____3062 = arg_as_list arg_as_string a2 in
             (match uu____3062 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3070 = string_as_const rng r in Some uu____3070
              | uu____3071 -> None)
         | uu____3074 -> None)
    | uu____3076 -> None in
  let string_of_int1 rng i =
    let uu____3087 = FStar_Util.string_of_int i in
    string_as_const rng uu____3087 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3103 = FStar_Util.string_of_int i in
    string_as_const rng uu____3103 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3122 =
      let uu____3132 =
        let uu____3142 =
          let uu____3152 =
            let uu____3162 =
              let uu____3172 =
                let uu____3182 =
                  let uu____3192 =
                    let uu____3202 =
                      let uu____3212 =
                        let uu____3222 =
                          let uu____3232 =
                            let uu____3242 =
                              let uu____3252 =
                                let uu____3262 =
                                  let uu____3272 =
                                    let uu____3282 =
                                      let uu____3292 =
                                        let uu____3301 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3301, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3307 =
                                        let uu____3317 =
                                          let uu____3326 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3326, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3333 =
                                          let uu____3343 =
                                            let uu____3355 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3355,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3343] in
                                        uu____3317 :: uu____3333 in
                                      uu____3292 :: uu____3307 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3282 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3272 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3262 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3252 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3242 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3232 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3222 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3212 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3202 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3192 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3182 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3172 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3162 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3152 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3142 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3132 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3122 in
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
      let uu____3679 =
        let uu____3680 =
          let uu____3681 = FStar_Syntax_Syntax.as_arg c in [uu____3681] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3680 in
      uu____3679 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3705 =
              let uu____3714 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3714, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3723  ->
                        fun uu____3724  ->
                          match (uu____3723, uu____3724) with
                          | ((int_to_t1,x),(uu____3735,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3741 =
              let uu____3751 =
                let uu____3760 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3760, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3769  ->
                          fun uu____3770  ->
                            match (uu____3769, uu____3770) with
                            | ((int_to_t1,x),(uu____3781,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3787 =
                let uu____3797 =
                  let uu____3806 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3806, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3815  ->
                            fun uu____3816  ->
                              match (uu____3815, uu____3816) with
                              | ((int_to_t1,x),(uu____3827,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3797] in
              uu____3751 :: uu____3787 in
            uu____3705 :: uu____3741)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3893)::(a1,uu____3895)::(a2,uu____3897)::[] ->
        let uu____3926 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3926 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3928 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3928
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3933 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3933
         | uu____3938 -> None)
    | uu____3939 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3952)::(a1,uu____3954)::(a2,uu____3956)::[] ->
        let uu____3985 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3985 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_3989 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_3989.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_3989.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_3989.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_3996 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_3996.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_3996.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_3996.FStar_Syntax_Syntax.vars)
                })
         | uu____4001 -> None)
    | (_typ,uu____4003)::uu____4004::(a1,uu____4006)::(a2,uu____4008)::[] ->
        let uu____4045 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4045 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4049 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4049.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4049.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4049.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4056 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4056.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4056.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4056.FStar_Syntax_Syntax.vars)
                })
         | uu____4061 -> None)
    | uu____4062 -> failwith "Unexpected number of arguments" in
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
      let uu____4073 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4073
      then tm
      else
        (let uu____4075 = FStar_Syntax_Util.head_and_args tm in
         match uu____4075 with
         | (head1,args) ->
             let uu____4101 =
               let uu____4102 = FStar_Syntax_Util.un_uinst head1 in
               uu____4102.FStar_Syntax_Syntax.n in
             (match uu____4101 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4106 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4106 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4118 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4118 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4121 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___163_4128 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4128.tcenv);
           delta_level = (uu___163_4128.delta_level);
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
        let uu___164_4150 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4150.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4150.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4150.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4169 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4196 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4196
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4199;
                     FStar_Syntax_Syntax.pos = uu____4200;
                     FStar_Syntax_Syntax.vars = uu____4201;_},uu____4202);
                FStar_Syntax_Syntax.tk = uu____4203;
                FStar_Syntax_Syntax.pos = uu____4204;
                FStar_Syntax_Syntax.vars = uu____4205;_},args)
             ->
             let uu____4225 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4225
             then
               let uu____4226 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4226 with
                | (Some (true ),uu____4259)::(uu____4260,(arg,uu____4262))::[]
                    -> arg
                | (uu____4303,(arg,uu____4305))::(Some (true ),uu____4306)::[]
                    -> arg
                | (Some (false ),uu____4347)::uu____4348::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4386::(Some (false ),uu____4387)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4425 -> tm)
             else
               (let uu____4435 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4435
                then
                  let uu____4436 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4436 with
                  | (Some (true ),uu____4469)::uu____4470::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4508::(Some (true ),uu____4509)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4547)::(uu____4548,(arg,uu____4550))::[]
                      -> arg
                  | (uu____4591,(arg,uu____4593))::(Some (false ),uu____4594)::[]
                      -> arg
                  | uu____4635 -> tm
                else
                  (let uu____4645 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4645
                   then
                     let uu____4646 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4646 with
                     | uu____4679::(Some (true ),uu____4680)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4718)::uu____4719::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4757)::(uu____4758,(arg,uu____4760))::[]
                         -> arg
                     | uu____4801 -> tm
                   else
                     (let uu____4811 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4811
                      then
                        let uu____4812 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4812 with
                        | (Some (true ),uu____4845)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4869)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4893 -> tm
                      else
                        (let uu____4903 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4903
                         then
                           match args with
                           | (t,uu____4905)::[] ->
                               let uu____4918 =
                                 let uu____4919 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4919.FStar_Syntax_Syntax.n in
                               (match uu____4918 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4922::[],body,uu____4924) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4950 -> tm)
                                | uu____4952 -> tm)
                           | (uu____4953,Some (FStar_Syntax_Syntax.Implicit
                              uu____4954))::(t,uu____4956)::[] ->
                               let uu____4983 =
                                 let uu____4984 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4984.FStar_Syntax_Syntax.n in
                               (match uu____4983 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4987::[],body,uu____4989) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5015 -> tm)
                                | uu____5017 -> tm)
                           | uu____5018 -> tm
                         else
                           (let uu____5025 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5025
                            then
                              match args with
                              | (t,uu____5027)::[] ->
                                  let uu____5040 =
                                    let uu____5041 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5041.FStar_Syntax_Syntax.n in
                                  (match uu____5040 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5044::[],body,uu____5046) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5072 -> tm)
                                   | uu____5074 -> tm)
                              | (uu____5075,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5076))::
                                  (t,uu____5078)::[] ->
                                  let uu____5105 =
                                    let uu____5106 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5106.FStar_Syntax_Syntax.n in
                                  (match uu____5105 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5109::[],body,uu____5111) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5137 -> tm)
                                   | uu____5139 -> tm)
                              | uu____5140 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5148;
                FStar_Syntax_Syntax.pos = uu____5149;
                FStar_Syntax_Syntax.vars = uu____5150;_},args)
             ->
             let uu____5166 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5166
             then
               let uu____5167 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5167 with
                | (Some (true ),uu____5200)::(uu____5201,(arg,uu____5203))::[]
                    -> arg
                | (uu____5244,(arg,uu____5246))::(Some (true ),uu____5247)::[]
                    -> arg
                | (Some (false ),uu____5288)::uu____5289::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5327::(Some (false ),uu____5328)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5366 -> tm)
             else
               (let uu____5376 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5376
                then
                  let uu____5377 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5377 with
                  | (Some (true ),uu____5410)::uu____5411::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5449::(Some (true ),uu____5450)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5488)::(uu____5489,(arg,uu____5491))::[]
                      -> arg
                  | (uu____5532,(arg,uu____5534))::(Some (false ),uu____5535)::[]
                      -> arg
                  | uu____5576 -> tm
                else
                  (let uu____5586 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5586
                   then
                     let uu____5587 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5587 with
                     | uu____5620::(Some (true ),uu____5621)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5659)::uu____5660::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5698)::(uu____5699,(arg,uu____5701))::[]
                         -> arg
                     | uu____5742 -> tm
                   else
                     (let uu____5752 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5752
                      then
                        let uu____5753 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5753 with
                        | (Some (true ),uu____5786)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5810)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5834 -> tm
                      else
                        (let uu____5844 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5844
                         then
                           match args with
                           | (t,uu____5846)::[] ->
                               let uu____5859 =
                                 let uu____5860 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5860.FStar_Syntax_Syntax.n in
                               (match uu____5859 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5863::[],body,uu____5865) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5891 -> tm)
                                | uu____5893 -> tm)
                           | (uu____5894,Some (FStar_Syntax_Syntax.Implicit
                              uu____5895))::(t,uu____5897)::[] ->
                               let uu____5924 =
                                 let uu____5925 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5925.FStar_Syntax_Syntax.n in
                               (match uu____5924 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5928::[],body,uu____5930) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5956 -> tm)
                                | uu____5958 -> tm)
                           | uu____5959 -> tm
                         else
                           (let uu____5966 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5966
                            then
                              match args with
                              | (t,uu____5968)::[] ->
                                  let uu____5981 =
                                    let uu____5982 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5982.FStar_Syntax_Syntax.n in
                                  (match uu____5981 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5985::[],body,uu____5987) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6013 -> tm)
                                   | uu____6015 -> tm)
                              | (uu____6016,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6017))::
                                  (t,uu____6019)::[] ->
                                  let uu____6046 =
                                    let uu____6047 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6047.FStar_Syntax_Syntax.n in
                                  (match uu____6046 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6050::[],body,uu____6052) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6078 -> tm)
                                   | uu____6080 -> tm)
                              | uu____6081 -> tm
                            else reduce_equality cfg tm)))))
         | uu____6088 -> tm)
let is_norm_request hd1 args =
  let uu____6103 =
    let uu____6107 =
      let uu____6108 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6108.FStar_Syntax_Syntax.n in
    (uu____6107, args) in
  match uu____6103 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6113::uu____6114::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6117::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6119 -> false
let get_norm_request args =
  match args with
  | uu____6138::(tm,uu____6140)::[] -> tm
  | (tm,uu____6150)::[] -> tm
  | uu____6155 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6162  ->
    match uu___140_6162 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6164;
           FStar_Syntax_Syntax.pos = uu____6165;
           FStar_Syntax_Syntax.vars = uu____6166;_},uu____6167,uu____6168))::uu____6169
        -> true
    | uu____6175 -> false
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
            (fun uu____6290  ->
               let uu____6291 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6292 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6293 =
                 let uu____6294 =
                   let uu____6296 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6296 in
                 stack_to_string uu____6294 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6291
                 uu____6292 uu____6293);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6308 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6329 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6338 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6339 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6340;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6341;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6346;
                 FStar_Syntax_Syntax.fv_delta = uu____6347;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6351;
                 FStar_Syntax_Syntax.fv_delta = uu____6352;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6353);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6386 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6386.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6386.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6386.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6412 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6412) && (is_norm_request hd1 args))
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
                 let uu___166_6425 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6425.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6425.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6430;
                  FStar_Syntax_Syntax.pos = uu____6431;
                  FStar_Syntax_Syntax.vars = uu____6432;_},a1::a2::rest)
               ->
               let uu____6466 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6466 with
                | (hd1,uu____6477) ->
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
                    (FStar_Const.Const_reflect uu____6532);
                  FStar_Syntax_Syntax.tk = uu____6533;
                  FStar_Syntax_Syntax.pos = uu____6534;
                  FStar_Syntax_Syntax.vars = uu____6535;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6558 = FStar_List.tl stack1 in
               norm cfg env uu____6558 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6561;
                  FStar_Syntax_Syntax.pos = uu____6562;
                  FStar_Syntax_Syntax.vars = uu____6563;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6586 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6586 with
                | (reify_head,uu____6597) ->
                    let a1 =
                      let uu____6613 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6613 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6616);
                            FStar_Syntax_Syntax.tk = uu____6617;
                            FStar_Syntax_Syntax.pos = uu____6618;
                            FStar_Syntax_Syntax.vars = uu____6619;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6644 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6652 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6652
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6659 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6659
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6662 =
                      let uu____6666 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6666, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6662 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6675  ->
                         match uu___141_6675 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6678 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     ((((((((FStar_Syntax_Syntax.fv_eq_lid f
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
                            FStar_Syntax_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Syntax_Const.false_lid)) in
                 if uu____6678 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6682 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6682 in
                  let uu____6683 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6683 with
                  | None  ->
                      (log cfg
                         (fun uu____6694  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6700  ->
                            let uu____6701 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6702 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6701 uu____6702);
                       (let t3 =
                          let uu____6704 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6704
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
                          | (UnivArgs (us',uu____6716))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6729 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6730 ->
                              let uu____6731 =
                                let uu____6732 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6732 in
                              failwith uu____6731
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6739 = lookup_bvar env x in
               (match uu____6739 with
                | Univ uu____6740 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6755 = FStar_ST.read r in
                      (match uu____6755 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6774  ->
                                 let uu____6775 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6776 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6775
                                   uu____6776);
                            (let uu____6777 =
                               let uu____6778 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6778.FStar_Syntax_Syntax.n in
                             match uu____6777 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6781 ->
                                 norm cfg env2 stack1 t'
                             | uu____6796 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6829)::uu____6830 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6835)::uu____6836 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6842,uu____6843))::stack_rest ->
                    (match c with
                     | Univ uu____6846 -> norm cfg (c :: env) stack_rest t1
                     | uu____6847 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6850::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6863  ->
                                         let uu____6864 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6864);
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
                                           (fun uu___142_6878  ->
                                              match uu___142_6878 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6879 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6881  ->
                                         let uu____6882 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6882);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6893  ->
                                         let uu____6894 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6894);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6895 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6902 ->
                                   let cfg1 =
                                     let uu___167_6910 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_6910.tcenv);
                                       delta_level =
                                         (uu___167_6910.delta_level);
                                       primitive_steps =
                                         (uu___167_6910.primitive_steps)
                                     } in
                                   let uu____6911 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6911)
                          | uu____6912::tl1 ->
                              (log cfg
                                 (fun uu____6922  ->
                                    let uu____6923 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6923);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_6947 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_6947.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6960  ->
                          let uu____6961 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6961);
                     norm cfg env stack2 t1)
                | (Debug uu____6962)::uu____6963 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6965 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6965
                    else
                      (let uu____6967 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6967 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6996 =
                                   let uu____7002 =
                                     let uu____7003 =
                                       let uu____7004 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7004 in
                                     FStar_All.pipe_right uu____7003
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7002
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6996
                                   (fun _0_32  -> Some _0_32)
                             | uu____7029 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7043  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7048  ->
                                 let uu____7049 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7049);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7059 = cfg in
                               let uu____7060 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7059.steps);
                                 tcenv = (uu___169_7059.tcenv);
                                 delta_level = (uu___169_7059.delta_level);
                                 primitive_steps = uu____7060
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7070)::uu____7071 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7075 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7075
                    else
                      (let uu____7077 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7077 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7106 =
                                   let uu____7112 =
                                     let uu____7113 =
                                       let uu____7114 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7114 in
                                     FStar_All.pipe_right uu____7113
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7112
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7106
                                   (fun _0_34  -> Some _0_34)
                             | uu____7139 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7153  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7158  ->
                                 let uu____7159 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7159);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7169 = cfg in
                               let uu____7170 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7169.steps);
                                 tcenv = (uu___169_7169.tcenv);
                                 delta_level = (uu___169_7169.delta_level);
                                 primitive_steps = uu____7170
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7180)::uu____7181 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7187 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7187
                    else
                      (let uu____7189 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7189 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7218 =
                                   let uu____7224 =
                                     let uu____7225 =
                                       let uu____7226 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7226 in
                                     FStar_All.pipe_right uu____7225
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7224
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7218
                                   (fun _0_36  -> Some _0_36)
                             | uu____7251 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7265  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7270  ->
                                 let uu____7271 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7271);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7281 = cfg in
                               let uu____7282 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7281.steps);
                                 tcenv = (uu___169_7281.tcenv);
                                 delta_level = (uu___169_7281.delta_level);
                                 primitive_steps = uu____7282
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7292)::uu____7293 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7298 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7298
                    else
                      (let uu____7300 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7300 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7329 =
                                   let uu____7335 =
                                     let uu____7336 =
                                       let uu____7337 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7337 in
                                     FStar_All.pipe_right uu____7336
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7335
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7329
                                   (fun _0_38  -> Some _0_38)
                             | uu____7362 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7376  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7381  ->
                                 let uu____7382 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7382);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7392 = cfg in
                               let uu____7393 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7392.steps);
                                 tcenv = (uu___169_7392.tcenv);
                                 delta_level = (uu___169_7392.delta_level);
                                 primitive_steps = uu____7393
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7403)::uu____7404 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7414 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7414
                    else
                      (let uu____7416 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7416 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7445 =
                                   let uu____7451 =
                                     let uu____7452 =
                                       let uu____7453 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7453 in
                                     FStar_All.pipe_right uu____7452
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7451
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7445
                                   (fun _0_40  -> Some _0_40)
                             | uu____7478 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7492  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7497  ->
                                 let uu____7498 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7498);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7508 = cfg in
                               let uu____7509 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7508.steps);
                                 tcenv = (uu___169_7508.tcenv);
                                 delta_level = (uu___169_7508.delta_level);
                                 primitive_steps = uu____7509
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7519 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7519
                    else
                      (let uu____7521 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7521 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7550 =
                                   let uu____7556 =
                                     let uu____7557 =
                                       let uu____7558 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7558 in
                                     FStar_All.pipe_right uu____7557
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7556
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7550
                                   (fun _0_42  -> Some _0_42)
                             | uu____7583 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7597  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7602  ->
                                 let uu____7603 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7603);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7613 = cfg in
                               let uu____7614 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7613.steps);
                                 tcenv = (uu___169_7613.tcenv);
                                 delta_level = (uu___169_7613.delta_level);
                                 primitive_steps = uu____7614
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
                      (fun uu____7646  ->
                         fun stack2  ->
                           match uu____7646 with
                           | (a,aq) ->
                               let uu____7654 =
                                 let uu____7655 =
                                   let uu____7659 =
                                     let uu____7660 =
                                       let uu____7670 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7670, false) in
                                     Clos uu____7660 in
                                   (uu____7659, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7655 in
                               uu____7654 :: stack2) args) in
               (log cfg
                  (fun uu____7692  ->
                     let uu____7693 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7693);
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
                             ((let uu___170_7714 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7714.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7714.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7715 ->
                      let uu____7718 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7718)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7721 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7721 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7737 =
                          let uu____7738 =
                            let uu____7743 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7744 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7744.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7744.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7743) in
                          FStar_Syntax_Syntax.Tm_refine uu____7738 in
                        mk uu____7737 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7757 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7757
               else
                 (let uu____7759 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7759 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7765 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7771  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7765 c1 in
                      let t2 =
                        let uu____7778 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7778 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7821)::uu____7822 -> norm cfg env stack1 t11
                | (Arg uu____7827)::uu____7828 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7833;
                       FStar_Syntax_Syntax.pos = uu____7834;
                       FStar_Syntax_Syntax.vars = uu____7835;_},uu____7836,uu____7837))::uu____7838
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7844)::uu____7845 ->
                    norm cfg env stack1 t11
                | uu____7850 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7853  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7866 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7866
                        | FStar_Util.Inr c ->
                            let uu____7874 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7874 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7879 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7879)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7930,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7931;
                              FStar_Syntax_Syntax.lbunivs = uu____7932;
                              FStar_Syntax_Syntax.lbtyp = uu____7933;
                              FStar_Syntax_Syntax.lbeff = uu____7934;
                              FStar_Syntax_Syntax.lbdef = uu____7935;_}::uu____7936),uu____7937)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7963 =
                 (let uu____7964 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7964) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7965 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7965))) in
               if uu____7963
               then
                 let env1 =
                   let uu____7968 =
                     let uu____7969 =
                       let uu____7979 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7979,
                         false) in
                     Clos uu____7969 in
                   uu____7968 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8003 =
                    let uu____8006 =
                      let uu____8007 =
                        let uu____8008 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8008
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8007] in
                    FStar_Syntax_Subst.open_term uu____8006 body in
                  match uu____8003 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8014 = lb in
                        let uu____8015 =
                          let uu____8018 =
                            let uu____8019 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8019
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8018
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____8028 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8031 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8015;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8014.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8028;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8014.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8031
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8041  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8057 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8057
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8070 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8092  ->
                        match uu____8092 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8131 =
                                let uu___173_8132 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8132.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8132.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8131 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8070 with
                | (rec_env,memos,uu____8192) ->
                    let uu____8207 =
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
                             let uu____8249 =
                               let uu____8250 =
                                 let uu____8260 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8260, false) in
                               Clos uu____8250 in
                             uu____8249 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8298;
                             FStar_Syntax_Syntax.pos = uu____8299;
                             FStar_Syntax_Syntax.vars = uu____8300;_},uu____8301,uu____8302))::uu____8303
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8309 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8316 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8316
                        then
                          let uu___174_8317 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8317.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8317.primitive_steps)
                          }
                        else
                          (let uu___175_8319 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8319.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8319.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8321 =
                         let uu____8322 = FStar_Syntax_Subst.compress head1 in
                         uu____8322.FStar_Syntax_Syntax.n in
                       match uu____8321 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8336 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8336 with
                            | (uu____8337,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8341 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8348 =
                                         let uu____8349 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8349.FStar_Syntax_Syntax.n in
                                       match uu____8348 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8354,uu____8355))
                                           ->
                                           let uu____8364 =
                                             let uu____8365 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8365.FStar_Syntax_Syntax.n in
                                           (match uu____8364 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8370,msrc,uu____8372))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8381 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8381
                                            | uu____8382 -> None)
                                       | uu____8383 -> None in
                                     let uu____8384 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8384 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8388 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8388.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8388.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8388.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8389 =
                                            FStar_List.tl stack1 in
                                          let uu____8390 =
                                            let uu____8391 =
                                              let uu____8394 =
                                                let uu____8395 =
                                                  let uu____8403 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8403) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8395 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8394 in
                                            uu____8391 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8389 uu____8390
                                      | None  ->
                                          let uu____8420 =
                                            let uu____8421 = is_return body in
                                            match uu____8421 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8424;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8425;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8426;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8431 -> false in
                                          if uu____8420
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
                                               let uu____8451 =
                                                 let uu____8454 =
                                                   let uu____8455 =
                                                     let uu____8470 =
                                                       let uu____8472 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8472] in
                                                     (uu____8470, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8455 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8454 in
                                               uu____8451 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8505 =
                                                 let uu____8506 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8506.FStar_Syntax_Syntax.n in
                                               match uu____8505 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8512::uu____8513::[])
                                                   ->
                                                   let uu____8519 =
                                                     let uu____8522 =
                                                       let uu____8523 =
                                                         let uu____8528 =
                                                           let uu____8530 =
                                                             let uu____8531 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8531 in
                                                           let uu____8532 =
                                                             let uu____8534 =
                                                               let uu____8535
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8535 in
                                                             [uu____8534] in
                                                           uu____8530 ::
                                                             uu____8532 in
                                                         (bind1, uu____8528) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8523 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8522 in
                                                   uu____8519 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8547 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8553 =
                                                 let uu____8556 =
                                                   let uu____8557 =
                                                     let uu____8567 =
                                                       let uu____8569 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8570 =
                                                         let uu____8572 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8573 =
                                                           let uu____8575 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8576 =
                                                             let uu____8578 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8579 =
                                                               let uu____8581
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8582
                                                                 =
                                                                 let uu____8584
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8584] in
                                                               uu____8581 ::
                                                                 uu____8582 in
                                                             uu____8578 ::
                                                               uu____8579 in
                                                           uu____8575 ::
                                                             uu____8576 in
                                                         uu____8572 ::
                                                           uu____8573 in
                                                       uu____8569 ::
                                                         uu____8570 in
                                                     (bind_inst, uu____8567) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8557 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8556 in
                                               uu____8553 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8596 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8596 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8614 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8614 with
                            | (uu____8615,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8638 =
                                        let uu____8639 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8639.FStar_Syntax_Syntax.n in
                                      match uu____8638 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8645) -> t4
                                      | uu____8650 -> head2 in
                                    let uu____8651 =
                                      let uu____8652 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8652.FStar_Syntax_Syntax.n in
                                    match uu____8651 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8657 -> None in
                                  let uu____8658 = maybe_extract_fv head2 in
                                  match uu____8658 with
                                  | Some x when
                                      let uu____8664 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8664
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8668 =
                                          maybe_extract_fv head3 in
                                        match uu____8668 with
                                        | Some uu____8671 -> Some true
                                        | uu____8672 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8675 -> (head2, None) in
                                ((let is_arg_impure uu____8686 =
                                    match uu____8686 with
                                    | (e,q) ->
                                        let uu____8691 =
                                          let uu____8692 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8692.FStar_Syntax_Syntax.n in
                                        (match uu____8691 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8707 -> false) in
                                  let uu____8708 =
                                    let uu____8709 =
                                      let uu____8713 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8713 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8709 in
                                  if uu____8708
                                  then
                                    let uu____8716 =
                                      let uu____8717 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8717 in
                                    failwith uu____8716
                                  else ());
                                 (let uu____8719 =
                                    maybe_unfold_action head_app in
                                  match uu____8719 with
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
                                      let uu____8754 = FStar_List.tl stack1 in
                                      norm cfg env uu____8754 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8768 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8768 in
                           let uu____8769 = FStar_List.tl stack1 in
                           norm cfg env uu____8769 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8852  ->
                                     match uu____8852 with
                                     | (pat,wopt,tm) ->
                                         let uu____8890 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8890))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8916 = FStar_List.tl stack1 in
                           norm cfg env uu____8916 tm
                       | uu____8917 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8926;
                             FStar_Syntax_Syntax.pos = uu____8927;
                             FStar_Syntax_Syntax.vars = uu____8928;_},uu____8929,uu____8930))::uu____8931
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8937 -> false in
                    if should_reify
                    then
                      let uu____8938 = FStar_List.tl stack1 in
                      let uu____8939 =
                        let uu____8940 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8940 in
                      norm cfg env uu____8938 uu____8939
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8943 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8943
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_8949 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_8949.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_8949.primitive_steps)
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
                | uu____8951 ->
                    (match stack1 with
                     | uu____8952::uu____8953 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8957)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8972 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8982 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8982
                           | uu____8989 -> m in
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
              let uu____9001 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9001 with
              | (uu____9002,return_repr) ->
                  let return_inst =
                    let uu____9009 =
                      let uu____9010 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9010.FStar_Syntax_Syntax.n in
                    match uu____9009 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9016::[])
                        ->
                        let uu____9022 =
                          let uu____9025 =
                            let uu____9026 =
                              let uu____9031 =
                                let uu____9033 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9033] in
                              (return_tm, uu____9031) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9026 in
                          FStar_Syntax_Syntax.mk uu____9025 in
                        uu____9022 None e.FStar_Syntax_Syntax.pos
                    | uu____9045 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9048 =
                    let uu____9051 =
                      let uu____9052 =
                        let uu____9062 =
                          let uu____9064 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9065 =
                            let uu____9067 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9067] in
                          uu____9064 :: uu____9065 in
                        (return_inst, uu____9062) in
                      FStar_Syntax_Syntax.Tm_app uu____9052 in
                    FStar_Syntax_Syntax.mk uu____9051 in
                  uu____9048 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9080 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9080 with
               | None  ->
                   let uu____9082 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9082
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9083;
                     FStar_TypeChecker_Env.mtarget = uu____9084;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9085;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9096;
                     FStar_TypeChecker_Env.mtarget = uu____9097;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9098;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9116 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9116)
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
                (fun uu____9146  ->
                   match uu____9146 with
                   | (a,imp) ->
                       let uu____9153 = norm cfg env [] a in
                       (uu____9153, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9168 = comp1 in
            let uu____9171 =
              let uu____9172 =
                let uu____9178 = norm cfg env [] t in
                let uu____9179 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9178, uu____9179) in
              FStar_Syntax_Syntax.Total uu____9172 in
            {
              FStar_Syntax_Syntax.n = uu____9171;
              FStar_Syntax_Syntax.tk = (uu___178_9168.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9168.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9168.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9194 = comp1 in
            let uu____9197 =
              let uu____9198 =
                let uu____9204 = norm cfg env [] t in
                let uu____9205 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9204, uu____9205) in
              FStar_Syntax_Syntax.GTotal uu____9198 in
            {
              FStar_Syntax_Syntax.n = uu____9197;
              FStar_Syntax_Syntax.tk = (uu___179_9194.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9194.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9194.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9236  ->
                      match uu____9236 with
                      | (a,i) ->
                          let uu____9243 = norm cfg env [] a in
                          (uu____9243, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9248  ->
                      match uu___143_9248 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9252 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9252
                      | f -> f)) in
            let uu___180_9256 = comp1 in
            let uu____9259 =
              let uu____9260 =
                let uu___181_9261 = ct in
                let uu____9262 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9263 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9266 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9262;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9261.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9263;
                  FStar_Syntax_Syntax.effect_args = uu____9266;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9260 in
            {
              FStar_Syntax_Syntax.n = uu____9259;
              FStar_Syntax_Syntax.tk = (uu___180_9256.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9256.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9256.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9283 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9283.tcenv);
               delta_level = (uu___182_9283.delta_level);
               primitive_steps = (uu___182_9283.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9288 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9288 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9291 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9305 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9305.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9305.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9305.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9315 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9315
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9320 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9320.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9320.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9320.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9320.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9322 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9322.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9322.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9322.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9322.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9323 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9323.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9323.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9323.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9329 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9332  ->
        match uu____9332 with
        | (x,imp) ->
            let uu____9335 =
              let uu___187_9336 = x in
              let uu____9337 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9336.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9336.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9337
              } in
            (uu____9335, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9343 =
          FStar_List.fold_left
            (fun uu____9350  ->
               fun b  ->
                 match uu____9350 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9343 with | (nbs,uu____9367) -> FStar_List.rev nbs
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
            let uu____9384 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9384
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9389 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9389
               then
                 let uu____9393 =
                   let uu____9396 =
                     let uu____9397 =
                       let uu____9400 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9400 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9397 in
                   FStar_Util.Inl uu____9396 in
                 Some uu____9393
               else
                 (let uu____9404 =
                    let uu____9407 =
                      let uu____9408 =
                        let uu____9411 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9411 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9408 in
                    FStar_Util.Inl uu____9407 in
                  Some uu____9404))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9424 -> lopt
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
              ((let uu____9436 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9436
                then
                  let uu____9437 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9438 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9437
                    uu____9438
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9449 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9449.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9469  ->
                    let uu____9470 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9470);
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
              let uu____9507 =
                let uu___189_9508 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9508.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9508.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9508.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9507
          | (Arg (Univ uu____9513,uu____9514,uu____9515))::uu____9516 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9518,uu____9519))::uu____9520 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9532),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9548  ->
                    let uu____9549 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9549);
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
                 (let uu____9560 = FStar_ST.read m in
                  match uu____9560 with
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
                  | Some (uu____9586,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9608 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9608
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9615  ->
                    let uu____9616 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9616);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9621 =
                  log cfg
                    (fun uu____9623  ->
                       let uu____9624 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9625 =
                         let uu____9626 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9633  ->
                                   match uu____9633 with
                                   | (p,uu____9639,uu____9640) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9626
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9624 uu____9625);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9650  ->
                               match uu___144_9650 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9651 -> false)) in
                     let steps' =
                       let uu____9654 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9654
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9657 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9657.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9657.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9691 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9707 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9741  ->
                                   fun uu____9742  ->
                                     match (uu____9741, uu____9742) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9807 = norm_pat env3 p1 in
                                         (match uu____9807 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9707 with
                          | (pats1,env3) ->
                              ((let uu___191_9873 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_9873.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_9873.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_9887 = x in
                           let uu____9888 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_9887.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_9887.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9888
                           } in
                         ((let uu___193_9894 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_9894.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_9894.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_9899 = x in
                           let uu____9900 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_9899.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_9899.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9900
                           } in
                         ((let uu___195_9906 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_9906.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_9906.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_9916 = x in
                           let uu____9917 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_9916.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_9916.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9917
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_9924 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_9924.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_9924.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9928 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9931 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9931 with
                                 | (p,wopt,e) ->
                                     let uu____9949 = norm_pat env1 p in
                                     (match uu____9949 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9973 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9973 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9978 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9978) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9988) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9993 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9994;
                        FStar_Syntax_Syntax.fv_delta = uu____9995;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9999;
                        FStar_Syntax_Syntax.fv_delta = uu____10000;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10001);_}
                      -> true
                  | uu____10008 -> false in
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
                  let uu____10107 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10107 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10139 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10141 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10143 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10155 ->
                                let uu____10156 =
                                  let uu____10157 = is_cons head1 in
                                  Prims.op_Negation uu____10157 in
                                FStar_Util.Inr uu____10156)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10171 =
                             let uu____10172 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10172.FStar_Syntax_Syntax.n in
                           (match uu____10171 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10179 ->
                                let uu____10180 =
                                  let uu____10181 = is_cons head1 in
                                  Prims.op_Negation uu____10181 in
                                FStar_Util.Inr uu____10180))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10215)::rest_a,(p1,uu____10218)::rest_p) ->
                      let uu____10246 = matches_pat t1 p1 in
                      (match uu____10246 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10260 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10331 = matches_pat scrutinee1 p1 in
                      (match uu____10331 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10341  ->
                                 let uu____10342 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10343 =
                                   let uu____10344 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10344
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10342 uu____10343);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10353 =
                                        let uu____10354 =
                                          let uu____10364 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10364, false) in
                                        Clos uu____10354 in
                                      uu____10353 :: env2) env1 s in
                             let uu____10387 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10387))) in
                let uu____10388 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10388
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10402  ->
                match uu___145_10402 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10405 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10409 -> d in
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
            let uu___198_10429 = config s e in
            {
              steps = (uu___198_10429.steps);
              tcenv = (uu___198_10429.tcenv);
              delta_level = (uu___198_10429.delta_level);
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
      fun t  -> let uu____10448 = config s e in norm_comp uu____10448 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10455 = config [] env in norm_universe uu____10455 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10462 = config [] env in ghost_to_pure_aux uu____10462 [] c
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
        let uu____10474 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10474 in
      let uu____10475 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10475
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10477 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10477.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10477.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10478  ->
                    let uu____10479 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10479))
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
            ((let uu____10492 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10492);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10501 = config [AllowUnboundUniverses] env in
          norm_comp uu____10501 [] c
        with
        | e ->
            ((let uu____10505 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10505);
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
                   let uu____10542 =
                     let uu____10543 =
                       let uu____10548 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10548) in
                     FStar_Syntax_Syntax.Tm_refine uu____10543 in
                   mk uu____10542 t01.FStar_Syntax_Syntax.pos
               | uu____10553 -> t2)
          | uu____10554 -> t2 in
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
        let uu____10576 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10576 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10592 ->
                 let uu____10596 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10596 with
                  | (actuals,uu____10607,uu____10608) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10630 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10630 with
                         | (binders,args) ->
                             let uu____10640 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10643 =
                               let uu____10650 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10650
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10640
                               uu____10643)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10686 =
        let uu____10690 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10690, (t.FStar_Syntax_Syntax.n)) in
      match uu____10686 with
      | (Some sort,uu____10697) ->
          let uu____10699 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10699
      | (uu____10700,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10704 ->
          let uu____10708 = FStar_Syntax_Util.head_and_args t in
          (match uu____10708 with
           | (head1,args) ->
               let uu____10734 =
                 let uu____10735 = FStar_Syntax_Subst.compress head1 in
                 uu____10735.FStar_Syntax_Syntax.n in
               (match uu____10734 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10738,thead) ->
                    let uu____10752 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10752 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10783 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_10787 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_10787.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_10787.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_10787.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_10787.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_10787.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_10787.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_10787.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_10787.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_10787.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_10787.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_10787.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_10787.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_10787.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_10787.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_10787.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_10787.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_10787.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_10787.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_10787.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_10787.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_10787.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_10787.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____10783 with
                            | (uu____10788,ty,uu____10790) ->
                                eta_expand_with_type env t ty))
                | uu____10791 ->
                    let uu____10792 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_10796 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_10796.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_10796.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_10796.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_10796.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_10796.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_10796.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_10796.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_10796.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_10796.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_10796.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_10796.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_10796.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_10796.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_10796.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_10796.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_10796.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_10796.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_10796.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_10796.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_10796.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_10796.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_10796.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____10792 with
                     | (uu____10797,ty,uu____10799) ->
                         eta_expand_with_type env t ty)))