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
      let tm1 = reduce_primops cfg tm in
      let uu____4197 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4197
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4200;
                     FStar_Syntax_Syntax.pos = uu____4201;
                     FStar_Syntax_Syntax.vars = uu____4202;_},uu____4203);
                FStar_Syntax_Syntax.tk = uu____4204;
                FStar_Syntax_Syntax.pos = uu____4205;
                FStar_Syntax_Syntax.vars = uu____4206;_},args)
             ->
             let uu____4226 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4226
             then
               let uu____4227 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4227 with
                | (Some (true ),uu____4260)::(uu____4261,(arg,uu____4263))::[]
                    -> arg
                | (uu____4304,(arg,uu____4306))::(Some (true ),uu____4307)::[]
                    -> arg
                | (Some (false ),uu____4348)::uu____4349::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4387::(Some (false ),uu____4388)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4426 -> tm1)
             else
               (let uu____4436 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4436
                then
                  let uu____4437 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4437 with
                  | (Some (true ),uu____4470)::uu____4471::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4509::(Some (true ),uu____4510)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4548)::(uu____4549,(arg,uu____4551))::[]
                      -> arg
                  | (uu____4592,(arg,uu____4594))::(Some (false ),uu____4595)::[]
                      -> arg
                  | uu____4636 -> tm1
                else
                  (let uu____4646 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4646
                   then
                     let uu____4647 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4647 with
                     | uu____4680::(Some (true ),uu____4681)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4719)::uu____4720::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4758)::(uu____4759,(arg,uu____4761))::[]
                         -> arg
                     | uu____4802 -> tm1
                   else
                     (let uu____4812 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4812
                      then
                        let uu____4813 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4813 with
                        | (Some (true ),uu____4846)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4870)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4894 -> tm1
                      else
                        (let uu____4904 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4904
                         then
                           match args with
                           | (t,uu____4906)::[] ->
                               let uu____4919 =
                                 let uu____4920 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4920.FStar_Syntax_Syntax.n in
                               (match uu____4919 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4923::[],body,uu____4925) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4951 -> tm1)
                                | uu____4953 -> tm1)
                           | (uu____4954,Some (FStar_Syntax_Syntax.Implicit
                              uu____4955))::(t,uu____4957)::[] ->
                               let uu____4984 =
                                 let uu____4985 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4985.FStar_Syntax_Syntax.n in
                               (match uu____4984 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4988::[],body,uu____4990) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5016 -> tm1)
                                | uu____5018 -> tm1)
                           | uu____5019 -> tm1
                         else
                           (let uu____5026 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5026
                            then
                              match args with
                              | (t,uu____5028)::[] ->
                                  let uu____5041 =
                                    let uu____5042 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5042.FStar_Syntax_Syntax.n in
                                  (match uu____5041 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5045::[],body,uu____5047) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5073 -> tm1)
                                   | uu____5075 -> tm1)
                              | (uu____5076,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5077))::
                                  (t,uu____5079)::[] ->
                                  let uu____5106 =
                                    let uu____5107 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5107.FStar_Syntax_Syntax.n in
                                  (match uu____5106 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5110::[],body,uu____5112) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5138 -> tm1)
                                   | uu____5140 -> tm1)
                              | uu____5141 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5149;
                FStar_Syntax_Syntax.pos = uu____5150;
                FStar_Syntax_Syntax.vars = uu____5151;_},args)
             ->
             let uu____5167 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5167
             then
               let uu____5168 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5168 with
                | (Some (true ),uu____5201)::(uu____5202,(arg,uu____5204))::[]
                    -> arg
                | (uu____5245,(arg,uu____5247))::(Some (true ),uu____5248)::[]
                    -> arg
                | (Some (false ),uu____5289)::uu____5290::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5328::(Some (false ),uu____5329)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5367 -> tm1)
             else
               (let uu____5377 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5377
                then
                  let uu____5378 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5378 with
                  | (Some (true ),uu____5411)::uu____5412::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5450::(Some (true ),uu____5451)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5489)::(uu____5490,(arg,uu____5492))::[]
                      -> arg
                  | (uu____5533,(arg,uu____5535))::(Some (false ),uu____5536)::[]
                      -> arg
                  | uu____5577 -> tm1
                else
                  (let uu____5587 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5587
                   then
                     let uu____5588 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5588 with
                     | uu____5621::(Some (true ),uu____5622)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5660)::uu____5661::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5699)::(uu____5700,(arg,uu____5702))::[]
                         -> arg
                     | uu____5743 -> tm1
                   else
                     (let uu____5753 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5753
                      then
                        let uu____5754 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5754 with
                        | (Some (true ),uu____5787)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5811)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5835 -> tm1
                      else
                        (let uu____5845 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5845
                         then
                           match args with
                           | (t,uu____5847)::[] ->
                               let uu____5860 =
                                 let uu____5861 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5861.FStar_Syntax_Syntax.n in
                               (match uu____5860 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5864::[],body,uu____5866) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5892 -> tm1)
                                | uu____5894 -> tm1)
                           | (uu____5895,Some (FStar_Syntax_Syntax.Implicit
                              uu____5896))::(t,uu____5898)::[] ->
                               let uu____5925 =
                                 let uu____5926 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5926.FStar_Syntax_Syntax.n in
                               (match uu____5925 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5929::[],body,uu____5931) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5957 -> tm1)
                                | uu____5959 -> tm1)
                           | uu____5960 -> tm1
                         else
                           (let uu____5967 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
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
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6014 -> tm1)
                                   | uu____6016 -> tm1)
                              | (uu____6017,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6018))::
                                  (t,uu____6020)::[] ->
                                  let uu____6047 =
                                    let uu____6048 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6048.FStar_Syntax_Syntax.n in
                                  (match uu____6047 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6051::[],body,uu____6053) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6079 -> tm1)
                                   | uu____6081 -> tm1)
                              | uu____6082 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6089 -> tm1)
let is_norm_request hd1 args =
  let uu____6104 =
    let uu____6108 =
      let uu____6109 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6109.FStar_Syntax_Syntax.n in
    (uu____6108, args) in
  match uu____6104 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6114::uu____6115::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6118::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6120 -> false
let get_norm_request args =
  match args with
  | uu____6139::(tm,uu____6141)::[] -> tm
  | (tm,uu____6151)::[] -> tm
  | uu____6156 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6163  ->
    match uu___140_6163 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6165;
           FStar_Syntax_Syntax.pos = uu____6166;
           FStar_Syntax_Syntax.vars = uu____6167;_},uu____6168,uu____6169))::uu____6170
        -> true
    | uu____6176 -> false
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
            (fun uu____6291  ->
               let uu____6292 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6293 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6294 =
                 let uu____6295 =
                   let uu____6297 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6297 in
                 stack_to_string uu____6295 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6292
                 uu____6293 uu____6294);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6309 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6330 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6339 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6340 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6341;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6342;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6347;
                 FStar_Syntax_Syntax.fv_delta = uu____6348;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6352;
                 FStar_Syntax_Syntax.fv_delta = uu____6353;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6354);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6387 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6387.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6387.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6387.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6413 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6413) && (is_norm_request hd1 args))
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
                 let uu___166_6426 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6426.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6426.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6431;
                  FStar_Syntax_Syntax.pos = uu____6432;
                  FStar_Syntax_Syntax.vars = uu____6433;_},a1::a2::rest)
               ->
               let uu____6467 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6467 with
                | (hd1,uu____6478) ->
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
                    (FStar_Const.Const_reflect uu____6533);
                  FStar_Syntax_Syntax.tk = uu____6534;
                  FStar_Syntax_Syntax.pos = uu____6535;
                  FStar_Syntax_Syntax.vars = uu____6536;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6559 = FStar_List.tl stack1 in
               norm cfg env uu____6559 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6562;
                  FStar_Syntax_Syntax.pos = uu____6563;
                  FStar_Syntax_Syntax.vars = uu____6564;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6587 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6587 with
                | (reify_head,uu____6598) ->
                    let a1 =
                      let uu____6614 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6614 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6617);
                            FStar_Syntax_Syntax.tk = uu____6618;
                            FStar_Syntax_Syntax.pos = uu____6619;
                            FStar_Syntax_Syntax.vars = uu____6620;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6645 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6653 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6653
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6660 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6660
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6663 =
                      let uu____6667 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6667, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6663 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6676  ->
                         match uu___141_6676 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6679 =
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
                 if uu____6679 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6683 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6683 in
                  let uu____6684 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6684 with
                  | None  ->
                      (log cfg
                         (fun uu____6695  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6701  ->
                            let uu____6702 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6703 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6702 uu____6703);
                       (let t3 =
                          let uu____6705 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6705
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
                          | (UnivArgs (us',uu____6717))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6730 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6731 ->
                              let uu____6732 =
                                let uu____6733 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6733 in
                              failwith uu____6732
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6740 = lookup_bvar env x in
               (match uu____6740 with
                | Univ uu____6741 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6756 = FStar_ST.read r in
                      (match uu____6756 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6775  ->
                                 let uu____6776 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6777 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6776
                                   uu____6777);
                            (let uu____6778 =
                               let uu____6779 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6779.FStar_Syntax_Syntax.n in
                             match uu____6778 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6782 ->
                                 norm cfg env2 stack1 t'
                             | uu____6797 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6830)::uu____6831 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6836)::uu____6837 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6843,uu____6844))::stack_rest ->
                    (match c with
                     | Univ uu____6847 -> norm cfg (c :: env) stack_rest t1
                     | uu____6848 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6851::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6864  ->
                                         let uu____6865 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6865);
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
                                           (fun uu___142_6879  ->
                                              match uu___142_6879 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6880 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6882  ->
                                         let uu____6883 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6883);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6894  ->
                                         let uu____6895 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6895);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6896 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6903 ->
                                   let cfg1 =
                                     let uu___167_6911 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_6911.tcenv);
                                       delta_level =
                                         (uu___167_6911.delta_level);
                                       primitive_steps =
                                         (uu___167_6911.primitive_steps)
                                     } in
                                   let uu____6912 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6912)
                          | uu____6913::tl1 ->
                              (log cfg
                                 (fun uu____6923  ->
                                    let uu____6924 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6924);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_6948 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_6948.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6961  ->
                          let uu____6962 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6962);
                     norm cfg env stack2 t1)
                | (Debug uu____6963)::uu____6964 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6966 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6966
                    else
                      (let uu____6968 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6968 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____6997 =
                                   let uu____7003 =
                                     let uu____7004 =
                                       let uu____7005 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7005 in
                                     FStar_All.pipe_right uu____7004
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7003
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6997
                                   (fun _0_32  -> Some _0_32)
                             | uu____7030 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7044  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7049  ->
                                 let uu____7050 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7050);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7060 = cfg in
                               let uu____7061 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7060.steps);
                                 tcenv = (uu___169_7060.tcenv);
                                 delta_level = (uu___169_7060.delta_level);
                                 primitive_steps = uu____7061
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7071)::uu____7072 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7076 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7076
                    else
                      (let uu____7078 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7078 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7107 =
                                   let uu____7113 =
                                     let uu____7114 =
                                       let uu____7115 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7115 in
                                     FStar_All.pipe_right uu____7114
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7113
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7107
                                   (fun _0_34  -> Some _0_34)
                             | uu____7140 -> lopt in
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
                               let uu___169_7170 = cfg in
                               let uu____7171 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7170.steps);
                                 tcenv = (uu___169_7170.tcenv);
                                 delta_level = (uu___169_7170.delta_level);
                                 primitive_steps = uu____7171
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7181)::uu____7182 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7188 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7188
                    else
                      (let uu____7190 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7190 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7219 =
                                   let uu____7225 =
                                     let uu____7226 =
                                       let uu____7227 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7227 in
                                     FStar_All.pipe_right uu____7226
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7225
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7219
                                   (fun _0_36  -> Some _0_36)
                             | uu____7252 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7266  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7271  ->
                                 let uu____7272 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7272);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7282 = cfg in
                               let uu____7283 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7282.steps);
                                 tcenv = (uu___169_7282.tcenv);
                                 delta_level = (uu___169_7282.delta_level);
                                 primitive_steps = uu____7283
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7293)::uu____7294 ->
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
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7330
                                   (fun _0_38  -> Some _0_38)
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
                               let uu___169_7393 = cfg in
                               let uu____7394 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7393.steps);
                                 tcenv = (uu___169_7393.tcenv);
                                 delta_level = (uu___169_7393.delta_level);
                                 primitive_steps = uu____7394
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7404)::uu____7405 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7415 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7415
                    else
                      (let uu____7417 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7417 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7446 =
                                   let uu____7452 =
                                     let uu____7453 =
                                       let uu____7454 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7454 in
                                     FStar_All.pipe_right uu____7453
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7452
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7446
                                   (fun _0_40  -> Some _0_40)
                             | uu____7479 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7493  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7498  ->
                                 let uu____7499 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7499);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7509 = cfg in
                               let uu____7510 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7509.steps);
                                 tcenv = (uu___169_7509.tcenv);
                                 delta_level = (uu___169_7509.delta_level);
                                 primitive_steps = uu____7510
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7520 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7520
                    else
                      (let uu____7522 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7522 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7551 =
                                   let uu____7557 =
                                     let uu____7558 =
                                       let uu____7559 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7559 in
                                     FStar_All.pipe_right uu____7558
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7557
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7551
                                   (fun _0_42  -> Some _0_42)
                             | uu____7584 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7598  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7603  ->
                                 let uu____7604 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7604);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7614 = cfg in
                               let uu____7615 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7614.steps);
                                 tcenv = (uu___169_7614.tcenv);
                                 delta_level = (uu___169_7614.delta_level);
                                 primitive_steps = uu____7615
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
                      (fun uu____7647  ->
                         fun stack2  ->
                           match uu____7647 with
                           | (a,aq) ->
                               let uu____7655 =
                                 let uu____7656 =
                                   let uu____7660 =
                                     let uu____7661 =
                                       let uu____7671 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7671, false) in
                                     Clos uu____7661 in
                                   (uu____7660, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7656 in
                               uu____7655 :: stack2) args) in
               (log cfg
                  (fun uu____7693  ->
                     let uu____7694 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7694);
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
                             ((let uu___170_7715 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7715.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7715.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7716 ->
                      let uu____7719 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7719)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7722 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7722 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7738 =
                          let uu____7739 =
                            let uu____7744 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7745 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7745.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7745.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7744) in
                          FStar_Syntax_Syntax.Tm_refine uu____7739 in
                        mk uu____7738 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7758 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7758
               else
                 (let uu____7760 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7760 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7766 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7772  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7766 c1 in
                      let t2 =
                        let uu____7779 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7779 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7822)::uu____7823 -> norm cfg env stack1 t11
                | (Arg uu____7828)::uu____7829 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7834;
                       FStar_Syntax_Syntax.pos = uu____7835;
                       FStar_Syntax_Syntax.vars = uu____7836;_},uu____7837,uu____7838))::uu____7839
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7845)::uu____7846 ->
                    norm cfg env stack1 t11
                | uu____7851 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7854  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7867 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7867
                        | FStar_Util.Inr c ->
                            let uu____7875 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7875 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7880 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7880)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7931,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7932;
                              FStar_Syntax_Syntax.lbunivs = uu____7933;
                              FStar_Syntax_Syntax.lbtyp = uu____7934;
                              FStar_Syntax_Syntax.lbeff = uu____7935;
                              FStar_Syntax_Syntax.lbdef = uu____7936;_}::uu____7937),uu____7938)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7964 =
                 (let uu____7965 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7965) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7966 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7966))) in
               if uu____7964
               then
                 let env1 =
                   let uu____7969 =
                     let uu____7970 =
                       let uu____7980 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7980,
                         false) in
                     Clos uu____7970 in
                   uu____7969 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8004 =
                    let uu____8007 =
                      let uu____8008 =
                        let uu____8009 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8009
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8008] in
                    FStar_Syntax_Subst.open_term uu____8007 body in
                  match uu____8004 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8015 = lb in
                        let uu____8016 =
                          let uu____8019 =
                            let uu____8020 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8020
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8019
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____8029 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8032 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8016;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8015.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8029;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8015.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8032
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8042  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8058 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8058
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8071 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8093  ->
                        match uu____8093 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8132 =
                                let uu___173_8133 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8133.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8133.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8132 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8071 with
                | (rec_env,memos,uu____8193) ->
                    let uu____8208 =
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
                             let uu____8250 =
                               let uu____8251 =
                                 let uu____8261 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8261, false) in
                               Clos uu____8251 in
                             uu____8250 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8299;
                             FStar_Syntax_Syntax.pos = uu____8300;
                             FStar_Syntax_Syntax.vars = uu____8301;_},uu____8302,uu____8303))::uu____8304
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8310 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8317 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8317
                        then
                          let uu___174_8318 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8318.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8318.primitive_steps)
                          }
                        else
                          (let uu___175_8320 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8320.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8320.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8322 =
                         let uu____8323 = FStar_Syntax_Subst.compress head1 in
                         uu____8323.FStar_Syntax_Syntax.n in
                       match uu____8322 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8337 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8337 with
                            | (uu____8338,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8342 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8349 =
                                         let uu____8350 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8350.FStar_Syntax_Syntax.n in
                                       match uu____8349 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8355,uu____8356))
                                           ->
                                           let uu____8365 =
                                             let uu____8366 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8366.FStar_Syntax_Syntax.n in
                                           (match uu____8365 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8371,msrc,uu____8373))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8382 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8382
                                            | uu____8383 -> None)
                                       | uu____8384 -> None in
                                     let uu____8385 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8385 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8389 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8389.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8389.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8389.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8390 =
                                            FStar_List.tl stack1 in
                                          let uu____8391 =
                                            let uu____8392 =
                                              let uu____8395 =
                                                let uu____8396 =
                                                  let uu____8404 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8404) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8396 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8395 in
                                            uu____8392 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8390 uu____8391
                                      | None  ->
                                          let uu____8421 =
                                            let uu____8422 = is_return body in
                                            match uu____8422 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8425;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8426;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8427;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8432 -> false in
                                          if uu____8421
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
                                               let uu____8452 =
                                                 let uu____8455 =
                                                   let uu____8456 =
                                                     let uu____8471 =
                                                       let uu____8473 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8473] in
                                                     (uu____8471, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8456 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8455 in
                                               uu____8452 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8506 =
                                                 let uu____8507 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8507.FStar_Syntax_Syntax.n in
                                               match uu____8506 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8513::uu____8514::[])
                                                   ->
                                                   let uu____8520 =
                                                     let uu____8523 =
                                                       let uu____8524 =
                                                         let uu____8529 =
                                                           let uu____8531 =
                                                             let uu____8532 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8532 in
                                                           let uu____8533 =
                                                             let uu____8535 =
                                                               let uu____8536
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8536 in
                                                             [uu____8535] in
                                                           uu____8531 ::
                                                             uu____8533 in
                                                         (bind1, uu____8529) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8524 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8523 in
                                                   uu____8520 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8548 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8554 =
                                                 let uu____8557 =
                                                   let uu____8558 =
                                                     let uu____8568 =
                                                       let uu____8570 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8571 =
                                                         let uu____8573 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8574 =
                                                           let uu____8576 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8577 =
                                                             let uu____8579 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8580 =
                                                               let uu____8582
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8583
                                                                 =
                                                                 let uu____8585
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8585] in
                                                               uu____8582 ::
                                                                 uu____8583 in
                                                             uu____8579 ::
                                                               uu____8580 in
                                                           uu____8576 ::
                                                             uu____8577 in
                                                         uu____8573 ::
                                                           uu____8574 in
                                                       uu____8570 ::
                                                         uu____8571 in
                                                     (bind_inst, uu____8568) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8558 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8557 in
                                               uu____8554 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8597 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8597 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8615 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8615 with
                            | (uu____8616,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8639 =
                                        let uu____8640 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8640.FStar_Syntax_Syntax.n in
                                      match uu____8639 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8646) -> t4
                                      | uu____8651 -> head2 in
                                    let uu____8652 =
                                      let uu____8653 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8653.FStar_Syntax_Syntax.n in
                                    match uu____8652 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8658 -> None in
                                  let uu____8659 = maybe_extract_fv head2 in
                                  match uu____8659 with
                                  | Some x when
                                      let uu____8665 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8665
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8669 =
                                          maybe_extract_fv head3 in
                                        match uu____8669 with
                                        | Some uu____8672 -> Some true
                                        | uu____8673 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8676 -> (head2, None) in
                                ((let is_arg_impure uu____8687 =
                                    match uu____8687 with
                                    | (e,q) ->
                                        let uu____8692 =
                                          let uu____8693 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8693.FStar_Syntax_Syntax.n in
                                        (match uu____8692 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8708 -> false) in
                                  let uu____8709 =
                                    let uu____8710 =
                                      let uu____8714 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8714 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8710 in
                                  if uu____8709
                                  then
                                    let uu____8717 =
                                      let uu____8718 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8718 in
                                    failwith uu____8717
                                  else ());
                                 (let uu____8720 =
                                    maybe_unfold_action head_app in
                                  match uu____8720 with
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
                                      let uu____8755 = FStar_List.tl stack1 in
                                      norm cfg env uu____8755 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8769 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8769 in
                           let uu____8770 = FStar_List.tl stack1 in
                           norm cfg env uu____8770 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8853  ->
                                     match uu____8853 with
                                     | (pat,wopt,tm) ->
                                         let uu____8891 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8891))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8917 = FStar_List.tl stack1 in
                           norm cfg env uu____8917 tm
                       | uu____8918 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8927;
                             FStar_Syntax_Syntax.pos = uu____8928;
                             FStar_Syntax_Syntax.vars = uu____8929;_},uu____8930,uu____8931))::uu____8932
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8938 -> false in
                    if should_reify
                    then
                      let uu____8939 = FStar_List.tl stack1 in
                      let uu____8940 =
                        let uu____8941 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8941 in
                      norm cfg env uu____8939 uu____8940
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8944 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8944
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_8950 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_8950.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_8950.primitive_steps)
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
                | uu____8952 ->
                    (match stack1 with
                     | uu____8953::uu____8954 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8958)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8973 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8983 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8983
                           | uu____8990 -> m in
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
              let uu____9002 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9002 with
              | (uu____9003,return_repr) ->
                  let return_inst =
                    let uu____9010 =
                      let uu____9011 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9011.FStar_Syntax_Syntax.n in
                    match uu____9010 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9017::[])
                        ->
                        let uu____9023 =
                          let uu____9026 =
                            let uu____9027 =
                              let uu____9032 =
                                let uu____9034 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9034] in
                              (return_tm, uu____9032) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9027 in
                          FStar_Syntax_Syntax.mk uu____9026 in
                        uu____9023 None e.FStar_Syntax_Syntax.pos
                    | uu____9046 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9049 =
                    let uu____9052 =
                      let uu____9053 =
                        let uu____9063 =
                          let uu____9065 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9066 =
                            let uu____9068 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9068] in
                          uu____9065 :: uu____9066 in
                        (return_inst, uu____9063) in
                      FStar_Syntax_Syntax.Tm_app uu____9053 in
                    FStar_Syntax_Syntax.mk uu____9052 in
                  uu____9049 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9081 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9081 with
               | None  ->
                   let uu____9083 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9083
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9084;
                     FStar_TypeChecker_Env.mtarget = uu____9085;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9086;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9097;
                     FStar_TypeChecker_Env.mtarget = uu____9098;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9099;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9117 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9117)
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
                (fun uu____9147  ->
                   match uu____9147 with
                   | (a,imp) ->
                       let uu____9154 = norm cfg env [] a in
                       (uu____9154, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9169 = comp1 in
            let uu____9172 =
              let uu____9173 =
                let uu____9179 = norm cfg env [] t in
                let uu____9180 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9179, uu____9180) in
              FStar_Syntax_Syntax.Total uu____9173 in
            {
              FStar_Syntax_Syntax.n = uu____9172;
              FStar_Syntax_Syntax.tk = (uu___178_9169.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9169.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9169.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9195 = comp1 in
            let uu____9198 =
              let uu____9199 =
                let uu____9205 = norm cfg env [] t in
                let uu____9206 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9205, uu____9206) in
              FStar_Syntax_Syntax.GTotal uu____9199 in
            {
              FStar_Syntax_Syntax.n = uu____9198;
              FStar_Syntax_Syntax.tk = (uu___179_9195.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9195.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9195.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9237  ->
                      match uu____9237 with
                      | (a,i) ->
                          let uu____9244 = norm cfg env [] a in
                          (uu____9244, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9249  ->
                      match uu___143_9249 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9253 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9253
                      | f -> f)) in
            let uu___180_9257 = comp1 in
            let uu____9260 =
              let uu____9261 =
                let uu___181_9262 = ct in
                let uu____9263 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9264 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9267 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9263;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9262.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9264;
                  FStar_Syntax_Syntax.effect_args = uu____9267;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9261 in
            {
              FStar_Syntax_Syntax.n = uu____9260;
              FStar_Syntax_Syntax.tk = (uu___180_9257.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9257.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9257.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9284 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9284.tcenv);
               delta_level = (uu___182_9284.delta_level);
               primitive_steps = (uu___182_9284.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9289 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9289 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9292 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9306 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9306.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9306.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9306.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9316 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9316
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9321 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9321.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9321.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9321.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9321.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9323 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9323.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9323.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9323.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9323.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9324 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9324.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9324.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9324.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9330 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9333  ->
        match uu____9333 with
        | (x,imp) ->
            let uu____9336 =
              let uu___187_9337 = x in
              let uu____9338 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9337.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9337.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9338
              } in
            (uu____9336, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9344 =
          FStar_List.fold_left
            (fun uu____9351  ->
               fun b  ->
                 match uu____9351 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9344 with | (nbs,uu____9368) -> FStar_List.rev nbs
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
            let uu____9385 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9385
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9390 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9390
               then
                 let uu____9394 =
                   let uu____9397 =
                     let uu____9398 =
                       let uu____9401 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9401 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9398 in
                   FStar_Util.Inl uu____9397 in
                 Some uu____9394
               else
                 (let uu____9405 =
                    let uu____9408 =
                      let uu____9409 =
                        let uu____9412 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9412 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9409 in
                    FStar_Util.Inl uu____9408 in
                  Some uu____9405))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9425 -> lopt
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
              ((let uu____9437 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9437
                then
                  let uu____9438 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9439 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9438
                    uu____9439
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9450 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9450.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9470  ->
                    let uu____9471 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9471);
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
              let uu____9508 =
                let uu___189_9509 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9509.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9509.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9509.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9508
          | (Arg (Univ uu____9514,uu____9515,uu____9516))::uu____9517 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9519,uu____9520))::uu____9521 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9533),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9549  ->
                    let uu____9550 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9550);
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
                 (let uu____9561 = FStar_ST.read m in
                  match uu____9561 with
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
                  | Some (uu____9587,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9609 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9609
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9616  ->
                    let uu____9617 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9617);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9622 =
                  log cfg
                    (fun uu____9624  ->
                       let uu____9625 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9626 =
                         let uu____9627 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9634  ->
                                   match uu____9634 with
                                   | (p,uu____9640,uu____9641) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9627
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9625 uu____9626);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9651  ->
                               match uu___144_9651 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9652 -> false)) in
                     let steps' =
                       let uu____9655 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9655
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9658 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9658.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9658.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9692 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9708 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9742  ->
                                   fun uu____9743  ->
                                     match (uu____9742, uu____9743) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9808 = norm_pat env3 p1 in
                                         (match uu____9808 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9708 with
                          | (pats1,env3) ->
                              ((let uu___191_9874 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_9874.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_9874.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_9888 = x in
                           let uu____9889 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_9888.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_9888.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9889
                           } in
                         ((let uu___193_9895 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_9895.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_9895.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_9900 = x in
                           let uu____9901 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_9900.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_9900.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9901
                           } in
                         ((let uu___195_9907 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_9907.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_9907.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_9917 = x in
                           let uu____9918 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_9917.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_9917.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9918
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_9925 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_9925.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_9925.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9929 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9932 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9932 with
                                 | (p,wopt,e) ->
                                     let uu____9950 = norm_pat env1 p in
                                     (match uu____9950 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9974 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9974 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9979 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9979) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9989) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9994 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9995;
                        FStar_Syntax_Syntax.fv_delta = uu____9996;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10000;
                        FStar_Syntax_Syntax.fv_delta = uu____10001;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10002);_}
                      -> true
                  | uu____10009 -> false in
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
                  let uu____10108 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10108 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10140 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10142 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10144 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10156 ->
                                let uu____10157 =
                                  let uu____10158 = is_cons head1 in
                                  Prims.op_Negation uu____10158 in
                                FStar_Util.Inr uu____10157)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10172 =
                             let uu____10173 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10173.FStar_Syntax_Syntax.n in
                           (match uu____10172 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10180 ->
                                let uu____10181 =
                                  let uu____10182 = is_cons head1 in
                                  Prims.op_Negation uu____10182 in
                                FStar_Util.Inr uu____10181))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10216)::rest_a,(p1,uu____10219)::rest_p) ->
                      let uu____10247 = matches_pat t1 p1 in
                      (match uu____10247 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10261 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10332 = matches_pat scrutinee1 p1 in
                      (match uu____10332 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10342  ->
                                 let uu____10343 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10344 =
                                   let uu____10345 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10345
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10343 uu____10344);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10354 =
                                        let uu____10355 =
                                          let uu____10365 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10365, false) in
                                        Clos uu____10355 in
                                      uu____10354 :: env2) env1 s in
                             let uu____10388 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10388))) in
                let uu____10389 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10389
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10403  ->
                match uu___145_10403 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10406 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10410 -> d in
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
            let uu___198_10430 = config s e in
            {
              steps = (uu___198_10430.steps);
              tcenv = (uu___198_10430.tcenv);
              delta_level = (uu___198_10430.delta_level);
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
      fun t  -> let uu____10449 = config s e in norm_comp uu____10449 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10456 = config [] env in norm_universe uu____10456 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10463 = config [] env in ghost_to_pure_aux uu____10463 [] c
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
        let uu____10475 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10475 in
      let uu____10476 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10476
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10478 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10478.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10478.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10479  ->
                    let uu____10480 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10480))
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
            ((let uu____10493 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10493);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10502 = config [AllowUnboundUniverses] env in
          norm_comp uu____10502 [] c
        with
        | e ->
            ((let uu____10506 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10506);
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
                   let uu____10543 =
                     let uu____10544 =
                       let uu____10549 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10549) in
                     FStar_Syntax_Syntax.Tm_refine uu____10544 in
                   mk uu____10543 t01.FStar_Syntax_Syntax.pos
               | uu____10554 -> t2)
          | uu____10555 -> t2 in
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
        let uu____10577 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10577 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10593 ->
                 let uu____10597 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10597 with
                  | (actuals,uu____10608,uu____10609) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10631 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10631 with
                         | (binders,args) ->
                             let uu____10641 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10644 =
                               let uu____10651 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10651
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10641
                               uu____10644)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10687 =
        let uu____10691 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10691, (t.FStar_Syntax_Syntax.n)) in
      match uu____10687 with
      | (Some sort,uu____10698) ->
          let uu____10700 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10700
      | (uu____10701,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10705 ->
          let uu____10709 = FStar_Syntax_Util.head_and_args t in
          (match uu____10709 with
           | (head1,args) ->
               let uu____10735 =
                 let uu____10736 = FStar_Syntax_Subst.compress head1 in
                 uu____10736.FStar_Syntax_Syntax.n in
               (match uu____10735 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10739,thead) ->
                    let uu____10753 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10753 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10784 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_10788 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_10788.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_10788.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_10788.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_10788.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_10788.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_10788.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_10788.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_10788.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_10788.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_10788.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_10788.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_10788.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_10788.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_10788.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_10788.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_10788.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_10788.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_10788.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_10788.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_10788.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_10788.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_10788.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____10784 with
                            | (uu____10789,ty,uu____10791) ->
                                eta_expand_with_type env t ty))
                | uu____10792 ->
                    let uu____10793 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_10797 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_10797.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_10797.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_10797.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_10797.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_10797.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_10797.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_10797.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_10797.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_10797.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_10797.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_10797.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_10797.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_10797.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_10797.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_10797.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_10797.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_10797.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_10797.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_10797.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_10797.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_10797.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_10797.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____10793 with
                     | (uu____10798,ty,uu____10800) ->
                         eta_expand_with_type env t ty)))