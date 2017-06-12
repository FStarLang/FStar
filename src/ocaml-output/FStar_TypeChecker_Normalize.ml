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
let is_fstar_tactics_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____640 =
      let uu____641 = FStar_Syntax_Util.un_uinst t in
      uu____641.FStar_Syntax_Syntax.n in
    match uu____640 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.by_tactic_lid
    | uu____645 -> false
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____685 = FStar_ST.read r in
  match uu____685 with
  | Some uu____690 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____699 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____699 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___136_704  ->
    match uu___136_704 with
    | Arg (c,uu____706,uu____707) ->
        let uu____708 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____708
    | MemoLazy uu____709 -> "MemoLazy"
    | Abs (uu____713,bs,uu____715,uu____716,uu____717) ->
        let uu____724 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____724
    | UnivArgs uu____731 -> "UnivArgs"
    | Match uu____735 -> "Match"
    | App (t,uu____740,uu____741) ->
        let uu____742 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____742
    | Meta (m,uu____744) -> "Meta"
    | Let uu____745 -> "Let"
    | Steps (uu____750,uu____751,uu____752) -> "Steps"
    | Debug t ->
        let uu____758 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____758
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____764 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____764 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____778 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____778 then f () else ()
let is_empty uu___137_787 =
  match uu___137_787 with | [] -> true | uu____789 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____807 ->
      let uu____808 =
        let uu____809 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____809 in
      failwith uu____808
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
          let uu____840 =
            FStar_List.fold_left
              (fun uu____849  ->
                 fun u1  ->
                   match uu____849 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____864 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____864 with
                        | (k_u,n1) ->
                            let uu____873 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____873
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____840 with
          | (uu____883,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____899 = FStar_List.nth env x in
                 match uu____899 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____902 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____906 ->
                   let uu____907 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____907
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____911 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____914 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____919 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____919 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____930 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____930 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____935 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____938 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____938 with
                                  | (uu____941,m) -> n1 <= m)) in
                        if uu____935 then rest1 else us1
                    | uu____945 -> us1)
               | uu____948 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____951 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____951 in
        let uu____953 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____953
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____955 = aux u in
           match uu____955 with
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
          (fun uu____1052  ->
             let uu____1053 = FStar_Syntax_Print.tag_of_term t in
             let uu____1054 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1053
               uu____1054);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1055 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1058 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1079 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1080 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1081 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1082 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1092 =
                    let uu____1093 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1093 in
                  mk uu____1092 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1100 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1100
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1102 = lookup_bvar env x in
                  (match uu____1102 with
                   | Univ uu____1103 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1107) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1175 = closures_as_binders_delayed cfg env bs in
                  (match uu____1175 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1195 =
                         let uu____1196 =
                           let uu____1211 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1211) in
                         FStar_Syntax_Syntax.Tm_abs uu____1196 in
                       mk uu____1195 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1241 = closures_as_binders_delayed cfg env bs in
                  (match uu____1241 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1272 =
                    let uu____1279 =
                      let uu____1283 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1283] in
                    closures_as_binders_delayed cfg env uu____1279 in
                  (match uu____1272 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1297 =
                         let uu____1298 =
                           let uu____1303 =
                             let uu____1304 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1304
                               FStar_Pervasives.fst in
                           (uu____1303, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1298 in
                       mk uu____1297 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1372 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1372
                    | FStar_Util.Inr c ->
                        let uu____1386 = close_comp cfg env c in
                        FStar_Util.Inr uu____1386 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1401 =
                    let uu____1402 =
                      let uu____1420 = closure_as_term_delayed cfg env t11 in
                      (uu____1420, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1402 in
                  mk uu____1401 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1458 =
                    let uu____1459 =
                      let uu____1464 = closure_as_term_delayed cfg env t' in
                      let uu____1467 =
                        let uu____1468 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1468 in
                      (uu____1464, uu____1467) in
                    FStar_Syntax_Syntax.Tm_meta uu____1459 in
                  mk uu____1458 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1510 =
                    let uu____1511 =
                      let uu____1516 = closure_as_term_delayed cfg env t' in
                      let uu____1519 =
                        let uu____1520 =
                          let uu____1525 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1525) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1520 in
                      (uu____1516, uu____1519) in
                    FStar_Syntax_Syntax.Tm_meta uu____1511 in
                  mk uu____1510 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1544 =
                    let uu____1545 =
                      let uu____1550 = closure_as_term_delayed cfg env t' in
                      let uu____1553 =
                        let uu____1554 =
                          let uu____1560 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1560) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1554 in
                      (uu____1550, uu____1553) in
                    FStar_Syntax_Syntax.Tm_meta uu____1545 in
                  mk uu____1544 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1573 =
                    let uu____1574 =
                      let uu____1579 = closure_as_term_delayed cfg env t' in
                      (uu____1579, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1574 in
                  mk uu____1573 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1600  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1611 -> body
                    | FStar_Util.Inl uu____1612 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___150_1614 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1614.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1614.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1614.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1621,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1645  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1650 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1650
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1654  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___151_1657 = lb in
                    let uu____1658 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1661 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1657.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1657.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1658;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1657.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1661
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1672  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1727 =
                    match uu____1727 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1773 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1789 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1823  ->
                                        fun uu____1824  ->
                                          match (uu____1823, uu____1824) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1889 =
                                                norm_pat env3 p1 in
                                              (match uu____1889 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1789 with
                               | (pats1,env3) ->
                                   ((let uu___152_1955 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_1955.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_1955.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___153_1969 = x in
                                let uu____1970 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_1969.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_1969.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1970
                                } in
                              ((let uu___154_1976 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_1976.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_1976.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___155_1981 = x in
                                let uu____1982 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_1981.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_1981.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1982
                                } in
                              ((let uu___156_1988 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_1988.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_1988.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___157_1998 = x in
                                let uu____1999 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_1998.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_1998.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1999
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___158_2006 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_2006.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_2006.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2009 = norm_pat env1 pat in
                        (match uu____2009 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2033 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2033 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2038 =
                    let uu____2039 =
                      let uu____2055 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2055) in
                    FStar_Syntax_Syntax.Tm_match uu____2039 in
                  mk uu____2038 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2108 -> closure_as_term cfg env t
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
        | uu____2124 ->
            FStar_List.map
              (fun uu____2134  ->
                 match uu____2134 with
                 | (x,imp) ->
                     let uu____2149 = closure_as_term_delayed cfg env x in
                     (uu____2149, imp)) args
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
        let uu____2161 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2185  ->
                  fun uu____2186  ->
                    match (uu____2185, uu____2186) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___159_2230 = b in
                          let uu____2231 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___159_2230.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___159_2230.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2231
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2161 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2278 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2290 = closure_as_term_delayed cfg env t in
                 let uu____2291 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2290 uu____2291
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2301 = closure_as_term_delayed cfg env t in
                 let uu____2302 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2301 uu____2302
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
                        (fun uu___138_2318  ->
                           match uu___138_2318 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2322 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2322
                           | f -> f)) in
                 let uu____2326 =
                   let uu___160_2327 = c1 in
                   let uu____2328 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2328;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___160_2327.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2326)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___139_2332  ->
            match uu___139_2332 with
            | FStar_Syntax_Syntax.DECREASES uu____2333 -> false
            | uu____2336 -> true))
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
            let uu____2364 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2364
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2381 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2381
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2407 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2431 =
      let uu____2432 =
        let uu____2438 = FStar_Util.string_of_int i in (uu____2438, None) in
      FStar_Const.Const_int uu____2432 in
    const_as_tm uu____2431 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2465 =
    match uu____2465 with
    | (a,uu____2470) ->
        let uu____2472 =
          let uu____2473 = FStar_Syntax_Subst.compress a in
          uu____2473.FStar_Syntax_Syntax.n in
        (match uu____2472 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2483 = FStar_Util.int_of_string i in Some uu____2483
         | uu____2484 -> None) in
  let arg_as_bounded_int uu____2493 =
    match uu____2493 with
    | (a,uu____2500) ->
        let uu____2504 =
          let uu____2505 = FStar_Syntax_Subst.compress a in
          uu____2505.FStar_Syntax_Syntax.n in
        (match uu____2504 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2512;
                FStar_Syntax_Syntax.pos = uu____2513;
                FStar_Syntax_Syntax.vars = uu____2514;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2516;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2517;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2518;_},uu____2519)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2550 =
               let uu____2553 = FStar_Util.int_of_string i in
               (fv1, uu____2553) in
             Some uu____2550
         | uu____2556 -> None) in
  let arg_as_bool uu____2565 =
    match uu____2565 with
    | (a,uu____2570) ->
        let uu____2572 =
          let uu____2573 = FStar_Syntax_Subst.compress a in
          uu____2573.FStar_Syntax_Syntax.n in
        (match uu____2572 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2578 -> None) in
  let arg_as_char uu____2585 =
    match uu____2585 with
    | (a,uu____2590) ->
        let uu____2592 =
          let uu____2593 = FStar_Syntax_Subst.compress a in
          uu____2593.FStar_Syntax_Syntax.n in
        (match uu____2592 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2598 -> None) in
  let arg_as_string uu____2605 =
    match uu____2605 with
    | (a,uu____2610) ->
        let uu____2612 =
          let uu____2613 = FStar_Syntax_Subst.compress a in
          uu____2613.FStar_Syntax_Syntax.n in
        (match uu____2612 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2618)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2621 -> None) in
  let arg_as_list f uu____2642 =
    match uu____2642 with
    | (a,uu____2651) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2670 -> None
          | (Some x)::xs ->
              let uu____2680 = sequence xs in
              (match uu____2680 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2691 = FStar_Syntax_Util.list_elements a in
        (match uu____2691 with
         | None  -> None
         | Some elts ->
             let uu____2701 =
               FStar_List.map
                 (fun x  ->
                    let uu____2706 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2706) elts in
             sequence uu____2701) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2736 = f a in Some uu____2736
    | uu____2737 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2776 = f a0 a1 in Some uu____2776
    | uu____2777 -> None in
  let unary_op as_a f r args =
    let uu____2821 = FStar_List.map as_a args in lift_unary (f r) uu____2821 in
  let binary_op as_a f r args =
    let uu____2871 = FStar_List.map as_a args in lift_binary (f r) uu____2871 in
  let as_primitive_step uu____2888 =
    match uu____2888 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2926 = f x in int_as_const r uu____2926) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2949 = f x y in int_as_const r uu____2949) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2966 = f x in bool_as_const r uu____2966) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2989 = f x y in bool_as_const r uu____2989) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3012 = f x y in string_as_const r uu____3012) in
  let list_of_string' rng s =
    let name l =
      let uu____3026 =
        let uu____3027 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3027 in
      mk uu____3026 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3037 =
      let uu____3039 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3039 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3037 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3093 = arg_as_string a1 in
        (match uu____3093 with
         | Some s1 ->
             let uu____3097 = arg_as_list arg_as_string a2 in
             (match uu____3097 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3105 = string_as_const rng r in Some uu____3105
              | uu____3106 -> None)
         | uu____3109 -> None)
    | uu____3111 -> None in
  let string_of_int1 rng i =
    let uu____3122 = FStar_Util.string_of_int i in
    string_as_const rng uu____3122 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3138 = FStar_Util.string_of_int i in
    string_as_const rng uu____3138 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3157 =
      let uu____3167 =
        let uu____3177 =
          let uu____3187 =
            let uu____3197 =
              let uu____3207 =
                let uu____3217 =
                  let uu____3227 =
                    let uu____3237 =
                      let uu____3247 =
                        let uu____3257 =
                          let uu____3267 =
                            let uu____3277 =
                              let uu____3287 =
                                let uu____3297 =
                                  let uu____3307 =
                                    let uu____3317 =
                                      let uu____3327 =
                                        let uu____3336 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3336, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3342 =
                                        let uu____3352 =
                                          let uu____3361 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3361, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3368 =
                                          let uu____3378 =
                                            let uu____3390 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3390,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3378] in
                                        uu____3352 :: uu____3368 in
                                      uu____3327 :: uu____3342 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3317 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3307 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3297 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3287 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3277 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3267 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3257 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3247 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3237 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3227 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3217 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3207 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3197 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3187 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3177 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3167 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3157 in
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
      let uu____3714 =
        let uu____3715 =
          let uu____3716 = FStar_Syntax_Syntax.as_arg c in [uu____3716] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3715 in
      uu____3714 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3740 =
              let uu____3749 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3749, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3758  ->
                        fun uu____3759  ->
                          match (uu____3758, uu____3759) with
                          | ((int_to_t1,x),(uu____3770,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3776 =
              let uu____3786 =
                let uu____3795 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3795, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3804  ->
                          fun uu____3805  ->
                            match (uu____3804, uu____3805) with
                            | ((int_to_t1,x),(uu____3816,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3822 =
                let uu____3832 =
                  let uu____3841 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3841, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3850  ->
                            fun uu____3851  ->
                              match (uu____3850, uu____3851) with
                              | ((int_to_t1,x),(uu____3862,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3832] in
              uu____3786 :: uu____3822 in
            uu____3740 :: uu____3776)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3937)::(a1,uu____3939)::(a2,uu____3941)::[] ->
        let uu____3970 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3970 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____3982 -> None)
    | uu____3983 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3996)::(a1,uu____3998)::(a2,uu____4000)::[] ->
        let uu____4029 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4029 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4033 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4033.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4033.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4033.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4040 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4040.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4040.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4040.FStar_Syntax_Syntax.vars)
                })
         | uu____4045 -> None)
    | (_typ,uu____4047)::uu____4048::(a1,uu____4050)::(a2,uu____4052)::[] ->
        let uu____4089 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4089 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4093 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4093.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4093.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4093.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4100 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4100.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4100.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4100.FStar_Syntax_Syntax.vars)
                })
         | uu____4105 -> None)
    | uu____4106 -> failwith "Unexpected number of arguments" in
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
      let uu____4118 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4118
      then tm
      else
        (let uu____4120 = FStar_Syntax_Util.head_and_args tm in
         match uu____4120 with
         | (head1,args) ->
             let uu____4146 =
               let uu____4147 = FStar_Syntax_Util.un_uinst head1 in
               uu____4147.FStar_Syntax_Syntax.n in
             (match uu____4146 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4151 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4151 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4166 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4166 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4169 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___163_4176 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4176.tcenv);
           delta_level = (uu___163_4176.delta_level);
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
        let uu___164_4198 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4198.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4198.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4198.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4217 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4245 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4245
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4248;
                     FStar_Syntax_Syntax.pos = uu____4249;
                     FStar_Syntax_Syntax.vars = uu____4250;_},uu____4251);
                FStar_Syntax_Syntax.tk = uu____4252;
                FStar_Syntax_Syntax.pos = uu____4253;
                FStar_Syntax_Syntax.vars = uu____4254;_},args)
             ->
             let uu____4274 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4274
             then
               let uu____4275 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4275 with
                | (Some (true ),uu____4308)::(uu____4309,(arg,uu____4311))::[]
                    -> arg
                | (uu____4352,(arg,uu____4354))::(Some (true ),uu____4355)::[]
                    -> arg
                | (Some (false ),uu____4396)::uu____4397::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4435::(Some (false ),uu____4436)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4474 -> tm1)
             else
               (let uu____4484 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4484
                then
                  let uu____4485 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4485 with
                  | (Some (true ),uu____4518)::uu____4519::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4557::(Some (true ),uu____4558)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4596)::(uu____4597,(arg,uu____4599))::[]
                      -> arg
                  | (uu____4640,(arg,uu____4642))::(Some (false ),uu____4643)::[]
                      -> arg
                  | uu____4684 -> tm1
                else
                  (let uu____4694 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4694
                   then
                     let uu____4695 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4695 with
                     | uu____4728::(Some (true ),uu____4729)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4767)::uu____4768::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4806)::(uu____4807,(arg,uu____4809))::[]
                         -> arg
                     | (uu____4850,(p,uu____4852))::(uu____4853,(q,uu____4855))::[]
                         ->
                         let uu____4897 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4897
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4899 -> tm1
                   else
                     (let uu____4909 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4909
                      then
                        let uu____4910 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4910 with
                        | (Some (true ),uu____4943)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4967)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4991 -> tm1
                      else
                        (let uu____5001 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5001
                         then
                           match args with
                           | (t,uu____5003)::[] ->
                               let uu____5016 =
                                 let uu____5017 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5017.FStar_Syntax_Syntax.n in
                               (match uu____5016 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5020::[],body,uu____5022) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5048 -> tm1)
                                | uu____5050 -> tm1)
                           | (uu____5051,Some (FStar_Syntax_Syntax.Implicit
                              uu____5052))::(t,uu____5054)::[] ->
                               let uu____5081 =
                                 let uu____5082 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5082.FStar_Syntax_Syntax.n in
                               (match uu____5081 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5085::[],body,uu____5087) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5113 -> tm1)
                                | uu____5115 -> tm1)
                           | uu____5116 -> tm1
                         else
                           (let uu____5123 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5123
                            then
                              match args with
                              | (t,uu____5125)::[] ->
                                  let uu____5138 =
                                    let uu____5139 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5139.FStar_Syntax_Syntax.n in
                                  (match uu____5138 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5142::[],body,uu____5144) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5170 -> tm1)
                                   | uu____5172 -> tm1)
                              | (uu____5173,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5174))::
                                  (t,uu____5176)::[] ->
                                  let uu____5203 =
                                    let uu____5204 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5204.FStar_Syntax_Syntax.n in
                                  (match uu____5203 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5207::[],body,uu____5209) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5235 -> tm1)
                                   | uu____5237 -> tm1)
                              | uu____5238 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5246;
                FStar_Syntax_Syntax.pos = uu____5247;
                FStar_Syntax_Syntax.vars = uu____5248;_},args)
             ->
             let uu____5264 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5264
             then
               let uu____5265 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5265 with
                | (Some (true ),uu____5298)::(uu____5299,(arg,uu____5301))::[]
                    -> arg
                | (uu____5342,(arg,uu____5344))::(Some (true ),uu____5345)::[]
                    -> arg
                | (Some (false ),uu____5386)::uu____5387::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5425::(Some (false ),uu____5426)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5464 -> tm1)
             else
               (let uu____5474 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5474
                then
                  let uu____5475 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5475 with
                  | (Some (true ),uu____5508)::uu____5509::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5547::(Some (true ),uu____5548)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5586)::(uu____5587,(arg,uu____5589))::[]
                      -> arg
                  | (uu____5630,(arg,uu____5632))::(Some (false ),uu____5633)::[]
                      -> arg
                  | uu____5674 -> tm1
                else
                  (let uu____5684 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5684
                   then
                     let uu____5685 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5685 with
                     | uu____5718::(Some (true ),uu____5719)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5757)::uu____5758::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5796)::(uu____5797,(arg,uu____5799))::[]
                         -> arg
                     | (uu____5840,(p,uu____5842))::(uu____5843,(q,uu____5845))::[]
                         ->
                         let uu____5887 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5887
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5889 -> tm1
                   else
                     (let uu____5899 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5899
                      then
                        let uu____5900 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5900 with
                        | (Some (true ),uu____5933)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5957)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5981 -> tm1
                      else
                        (let uu____5991 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
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
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6038 -> tm1)
                                | uu____6040 -> tm1)
                           | (uu____6041,Some (FStar_Syntax_Syntax.Implicit
                              uu____6042))::(t,uu____6044)::[] ->
                               let uu____6071 =
                                 let uu____6072 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6072.FStar_Syntax_Syntax.n in
                               (match uu____6071 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6075::[],body,uu____6077) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6103 -> tm1)
                                | uu____6105 -> tm1)
                           | uu____6106 -> tm1
                         else
                           (let uu____6113 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6113
                            then
                              match args with
                              | (t,uu____6115)::[] ->
                                  let uu____6128 =
                                    let uu____6129 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6129.FStar_Syntax_Syntax.n in
                                  (match uu____6128 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6132::[],body,uu____6134) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6160 -> tm1)
                                   | uu____6162 -> tm1)
                              | (uu____6163,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6164))::
                                  (t,uu____6166)::[] ->
                                  let uu____6193 =
                                    let uu____6194 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6194.FStar_Syntax_Syntax.n in
                                  (match uu____6193 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6197::[],body,uu____6199) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6225 -> tm1)
                                   | uu____6227 -> tm1)
                              | uu____6228 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6235 -> tm1)
let is_norm_request hd1 args =
  let uu____6250 =
    let uu____6254 =
      let uu____6255 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6255.FStar_Syntax_Syntax.n in
    (uu____6254, args) in
  match uu____6250 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6260::uu____6261::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6264::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6266 -> false
let get_norm_request args =
  match args with
  | uu____6285::(tm,uu____6287)::[] -> tm
  | (tm,uu____6297)::[] -> tm
  | uu____6302 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6309  ->
    match uu___140_6309 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6311;
           FStar_Syntax_Syntax.pos = uu____6312;
           FStar_Syntax_Syntax.vars = uu____6313;_},uu____6314,uu____6315))::uu____6316
        -> true
    | uu____6322 -> false
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
            (fun uu____6440  ->
               let uu____6441 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6442 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6443 =
                 let uu____6444 =
                   let uu____6446 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6446 in
                 stack_to_string uu____6444 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6441
                 uu____6442 uu____6443);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6458 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6479 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6488 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6489 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6490;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6491;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6496;
                 FStar_Syntax_Syntax.fv_delta = uu____6497;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6501;
                 FStar_Syntax_Syntax.fv_delta = uu____6502;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6503);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (is_fstar_tactics_embed hd1) ||
                 (is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6536 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6536.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6536.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6536.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6562 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6562) && (is_norm_request hd1 args))
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
                 let uu___166_6575 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6575.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6575.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6580;
                  FStar_Syntax_Syntax.pos = uu____6581;
                  FStar_Syntax_Syntax.vars = uu____6582;_},a1::a2::rest)
               ->
               let uu____6616 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6616 with
                | (hd1,uu____6627) ->
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
                    (FStar_Const.Const_reflect uu____6682);
                  FStar_Syntax_Syntax.tk = uu____6683;
                  FStar_Syntax_Syntax.pos = uu____6684;
                  FStar_Syntax_Syntax.vars = uu____6685;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6708 = FStar_List.tl stack1 in
               norm cfg env uu____6708 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6711;
                  FStar_Syntax_Syntax.pos = uu____6712;
                  FStar_Syntax_Syntax.vars = uu____6713;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6736 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6736 with
                | (reify_head,uu____6747) ->
                    let a1 =
                      let uu____6763 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6763 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6766);
                            FStar_Syntax_Syntax.tk = uu____6767;
                            FStar_Syntax_Syntax.pos = uu____6768;
                            FStar_Syntax_Syntax.vars = uu____6769;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6794 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6802 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6802
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6809 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6809
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6812 =
                      let uu____6816 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6816, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6812 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6825  ->
                         match uu___141_6825 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6828 =
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
                 if uu____6828 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6832 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6832 in
                  let uu____6833 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6833 with
                  | None  ->
                      (log cfg
                         (fun uu____6844  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6850  ->
                            let uu____6851 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6852 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6851 uu____6852);
                       (let t3 =
                          let uu____6854 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6854
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
                          | (UnivArgs (us',uu____6870))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6883 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6884 ->
                              let uu____6885 =
                                let uu____6886 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6886 in
                              failwith uu____6885
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6893 = lookup_bvar env x in
               (match uu____6893 with
                | Univ uu____6894 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6909 = FStar_ST.read r in
                      (match uu____6909 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6928  ->
                                 let uu____6929 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6930 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6929
                                   uu____6930);
                            (let uu____6931 =
                               let uu____6932 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6932.FStar_Syntax_Syntax.n in
                             match uu____6931 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6935 ->
                                 norm cfg env2 stack1 t'
                             | uu____6950 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6983)::uu____6984 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6989)::uu____6990 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6996,uu____6997))::stack_rest ->
                    (match c with
                     | Univ uu____7000 -> norm cfg (c :: env) stack_rest t1
                     | uu____7001 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____7004::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____7017  ->
                                         let uu____7018 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7018);
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
                                           (fun uu___142_7032  ->
                                              match uu___142_7032 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____7033 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7035  ->
                                         let uu____7036 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7036);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____7047  ->
                                         let uu____7048 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7048);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____7049 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7056 ->
                                   let cfg1 =
                                     let uu___167_7064 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_7064.tcenv);
                                       delta_level =
                                         (uu___167_7064.delta_level);
                                       primitive_steps =
                                         (uu___167_7064.primitive_steps)
                                     } in
                                   let uu____7065 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7065)
                          | uu____7066::tl1 ->
                              (log cfg
                                 (fun uu____7076  ->
                                    let uu____7077 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7077);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_7101 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_7101.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7114  ->
                          let uu____7115 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7115);
                     norm cfg env stack2 t1)
                | (Debug uu____7116)::uu____7117 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7119 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7119
                    else
                      (let uu____7121 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7121 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7150 =
                                   let uu____7156 =
                                     let uu____7157 =
                                       let uu____7158 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7158 in
                                     FStar_All.pipe_right uu____7157
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7156
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7150
                                   (fun _0_42  -> Some _0_42)
                             | uu____7183 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7197  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7202  ->
                                 let uu____7203 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7203);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7215 = cfg in
                               let uu____7216 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7215.steps);
                                 tcenv = (uu___169_7215.tcenv);
                                 delta_level = (uu___169_7215.delta_level);
                                 primitive_steps = uu____7216
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7226)::uu____7227 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7231 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7231
                    else
                      (let uu____7233 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7233 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7262 =
                                   let uu____7268 =
                                     let uu____7269 =
                                       let uu____7270 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7270 in
                                     FStar_All.pipe_right uu____7269
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7268
                                     (fun _0_43  -> FStar_Util.Inl _0_43) in
                                 FStar_All.pipe_right uu____7262
                                   (fun _0_44  -> Some _0_44)
                             | uu____7295 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7309  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7314  ->
                                 let uu____7315 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7315);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7327 = cfg in
                               let uu____7328 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7327.steps);
                                 tcenv = (uu___169_7327.tcenv);
                                 delta_level = (uu___169_7327.delta_level);
                                 primitive_steps = uu____7328
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7338)::uu____7339 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7345 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7345
                    else
                      (let uu____7347 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7347 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7376 =
                                   let uu____7382 =
                                     let uu____7383 =
                                       let uu____7384 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7384 in
                                     FStar_All.pipe_right uu____7383
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7382
                                     (fun _0_45  -> FStar_Util.Inl _0_45) in
                                 FStar_All.pipe_right uu____7376
                                   (fun _0_46  -> Some _0_46)
                             | uu____7409 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7423  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7428  ->
                                 let uu____7429 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7429);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7441 = cfg in
                               let uu____7442 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7441.steps);
                                 tcenv = (uu___169_7441.tcenv);
                                 delta_level = (uu___169_7441.delta_level);
                                 primitive_steps = uu____7442
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7452)::uu____7453 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7458 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7458
                    else
                      (let uu____7460 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7460 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7489 =
                                   let uu____7495 =
                                     let uu____7496 =
                                       let uu____7497 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7497 in
                                     FStar_All.pipe_right uu____7496
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7495
                                     (fun _0_47  -> FStar_Util.Inl _0_47) in
                                 FStar_All.pipe_right uu____7489
                                   (fun _0_48  -> Some _0_48)
                             | uu____7522 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7536  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7541  ->
                                 let uu____7542 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7542);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7554 = cfg in
                               let uu____7555 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7554.steps);
                                 tcenv = (uu___169_7554.tcenv);
                                 delta_level = (uu___169_7554.delta_level);
                                 primitive_steps = uu____7555
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7565)::uu____7566 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7576 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7576
                    else
                      (let uu____7578 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7578 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7607 =
                                   let uu____7613 =
                                     let uu____7614 =
                                       let uu____7615 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7615 in
                                     FStar_All.pipe_right uu____7614
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7613
                                     (fun _0_49  -> FStar_Util.Inl _0_49) in
                                 FStar_All.pipe_right uu____7607
                                   (fun _0_50  -> Some _0_50)
                             | uu____7640 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7654  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7659  ->
                                 let uu____7660 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7660);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7672 = cfg in
                               let uu____7673 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7672.steps);
                                 tcenv = (uu___169_7672.tcenv);
                                 delta_level = (uu___169_7672.delta_level);
                                 primitive_steps = uu____7673
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7683 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7683
                    else
                      (let uu____7685 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7685 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7714 =
                                   let uu____7720 =
                                     let uu____7721 =
                                       let uu____7722 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7722 in
                                     FStar_All.pipe_right uu____7721
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7720
                                     (fun _0_51  -> FStar_Util.Inl _0_51) in
                                 FStar_All.pipe_right uu____7714
                                   (fun _0_52  -> Some _0_52)
                             | uu____7747 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7761  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7766  ->
                                 let uu____7767 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7767);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7779 = cfg in
                               let uu____7780 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7779.steps);
                                 tcenv = (uu___169_7779.tcenv);
                                 delta_level = (uu___169_7779.delta_level);
                                 primitive_steps = uu____7780
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
                      (fun uu____7812  ->
                         fun stack2  ->
                           match uu____7812 with
                           | (a,aq) ->
                               let uu____7820 =
                                 let uu____7821 =
                                   let uu____7825 =
                                     let uu____7826 =
                                       let uu____7836 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7836, false) in
                                     Clos uu____7826 in
                                   (uu____7825, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7821 in
                               uu____7820 :: stack2) args) in
               (log cfg
                  (fun uu____7858  ->
                     let uu____7859 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7859);
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
                             ((let uu___170_7882 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7882.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7882.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7883 ->
                      let uu____7886 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7886)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7889 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7889 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7905 =
                          let uu____7906 =
                            let uu____7911 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7912 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7912.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7912.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7911) in
                          FStar_Syntax_Syntax.Tm_refine uu____7906 in
                        mk uu____7905 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7925 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7925
               else
                 (let uu____7927 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7927 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7933 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7939  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7933 c1 in
                      let t2 =
                        let uu____7946 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7946 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7989)::uu____7990 -> norm cfg env stack1 t11
                | (Arg uu____7995)::uu____7996 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____8001;
                       FStar_Syntax_Syntax.pos = uu____8002;
                       FStar_Syntax_Syntax.vars = uu____8003;_},uu____8004,uu____8005))::uu____8006
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____8012)::uu____8013 ->
                    norm cfg env stack1 t11
                | uu____8018 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____8021  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____8034 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____8034
                        | FStar_Util.Inr c ->
                            let uu____8042 = norm_comp cfg env c in
                            FStar_Util.Inr uu____8042 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____8047 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____8047)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____8098,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____8099;
                              FStar_Syntax_Syntax.lbunivs = uu____8100;
                              FStar_Syntax_Syntax.lbtyp = uu____8101;
                              FStar_Syntax_Syntax.lbeff = uu____8102;
                              FStar_Syntax_Syntax.lbdef = uu____8103;_}::uu____8104),uu____8105)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8131 =
                 (let uu____8132 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8132) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8133 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8133))) in
               if uu____8131
               then
                 let env1 =
                   let uu____8136 =
                     let uu____8137 =
                       let uu____8147 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8147,
                         false) in
                     Clos uu____8137 in
                   uu____8136 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8171 =
                    let uu____8174 =
                      let uu____8175 =
                        let uu____8176 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8176
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8175] in
                    FStar_Syntax_Subst.open_term uu____8174 body in
                  match uu____8171 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8182 = lb in
                        let uu____8183 =
                          let uu____8186 =
                            let uu____8187 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8187
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8186
                            (fun _0_53  -> FStar_Util.Inl _0_53) in
                        let uu____8196 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8199 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8183;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8182.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8196;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8182.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8199
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8209  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8225 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8225
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8238 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8260  ->
                        match uu____8260 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8299 =
                                let uu___173_8300 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8300.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8300.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8299 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8238 with
                | (rec_env,memos,uu____8360) ->
                    let uu____8375 =
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
                             let uu____8417 =
                               let uu____8418 =
                                 let uu____8428 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8428, false) in
                               Clos uu____8418 in
                             uu____8417 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8466;
                             FStar_Syntax_Syntax.pos = uu____8467;
                             FStar_Syntax_Syntax.vars = uu____8468;_},uu____8469,uu____8470))::uu____8471
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8477 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8484 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8484
                        then
                          let uu___174_8485 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8485.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8485.primitive_steps)
                          }
                        else
                          (let uu___175_8487 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8487.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8487.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8489 =
                         let uu____8490 = FStar_Syntax_Subst.compress head1 in
                         uu____8490.FStar_Syntax_Syntax.n in
                       match uu____8489 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8504 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8504 with
                            | (uu____8505,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8509 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8516 =
                                         let uu____8517 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8517.FStar_Syntax_Syntax.n in
                                       match uu____8516 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8522,uu____8523))
                                           ->
                                           let uu____8532 =
                                             let uu____8533 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8533.FStar_Syntax_Syntax.n in
                                           (match uu____8532 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8538,msrc,uu____8540))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8549 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8549
                                            | uu____8550 -> None)
                                       | uu____8551 -> None in
                                     let uu____8552 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8552 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8556 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8556.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8556.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8556.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8557 =
                                            FStar_List.tl stack1 in
                                          let uu____8558 =
                                            let uu____8559 =
                                              let uu____8562 =
                                                let uu____8563 =
                                                  let uu____8571 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8571) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8563 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8562 in
                                            uu____8559 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8557 uu____8558
                                      | None  ->
                                          let uu____8588 =
                                            let uu____8589 = is_return body in
                                            match uu____8589 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8592;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8593;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8594;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8599 -> false in
                                          if uu____8588
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
                                               let uu____8619 =
                                                 let uu____8622 =
                                                   let uu____8623 =
                                                     let uu____8638 =
                                                       let uu____8640 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8640] in
                                                     (uu____8638, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8623 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8622 in
                                               uu____8619 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8673 =
                                                 let uu____8674 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8674.FStar_Syntax_Syntax.n in
                                               match uu____8673 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8680::uu____8681::[])
                                                   ->
                                                   let uu____8687 =
                                                     let uu____8690 =
                                                       let uu____8691 =
                                                         let uu____8696 =
                                                           let uu____8698 =
                                                             let uu____8699 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8699 in
                                                           let uu____8700 =
                                                             let uu____8702 =
                                                               let uu____8703
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8703 in
                                                             [uu____8702] in
                                                           uu____8698 ::
                                                             uu____8700 in
                                                         (bind1, uu____8696) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8691 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8690 in
                                                   uu____8687 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8715 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8721 =
                                                 let uu____8724 =
                                                   let uu____8725 =
                                                     let uu____8735 =
                                                       let uu____8737 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8738 =
                                                         let uu____8740 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8741 =
                                                           let uu____8743 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8744 =
                                                             let uu____8746 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8747 =
                                                               let uu____8749
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8750
                                                                 =
                                                                 let uu____8752
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8752] in
                                                               uu____8749 ::
                                                                 uu____8750 in
                                                             uu____8746 ::
                                                               uu____8747 in
                                                           uu____8743 ::
                                                             uu____8744 in
                                                         uu____8740 ::
                                                           uu____8741 in
                                                       uu____8737 ::
                                                         uu____8738 in
                                                     (bind_inst, uu____8735) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8725 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8724 in
                                               uu____8721 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8764 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8764 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8782 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8782 with
                            | (uu____8783,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8806 =
                                        let uu____8807 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8807.FStar_Syntax_Syntax.n in
                                      match uu____8806 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8813) -> t4
                                      | uu____8818 -> head2 in
                                    let uu____8819 =
                                      let uu____8820 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8820.FStar_Syntax_Syntax.n in
                                    match uu____8819 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8825 -> None in
                                  let uu____8826 = maybe_extract_fv head2 in
                                  match uu____8826 with
                                  | Some x when
                                      let uu____8832 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8832
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8836 =
                                          maybe_extract_fv head3 in
                                        match uu____8836 with
                                        | Some uu____8839 -> Some true
                                        | uu____8840 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8843 -> (head2, None) in
                                ((let is_arg_impure uu____8854 =
                                    match uu____8854 with
                                    | (e,q) ->
                                        let uu____8859 =
                                          let uu____8860 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8860.FStar_Syntax_Syntax.n in
                                        (match uu____8859 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8875 -> false) in
                                  let uu____8876 =
                                    let uu____8877 =
                                      let uu____8881 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8881 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8877 in
                                  if uu____8876
                                  then
                                    let uu____8884 =
                                      let uu____8885 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8885 in
                                    failwith uu____8884
                                  else ());
                                 (let uu____8887 =
                                    maybe_unfold_action head_app in
                                  match uu____8887 with
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
                                      let uu____8922 = FStar_List.tl stack1 in
                                      norm cfg env uu____8922 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8936 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8936 in
                           let uu____8937 = FStar_List.tl stack1 in
                           norm cfg env uu____8937 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____9020  ->
                                     match uu____9020 with
                                     | (pat,wopt,tm) ->
                                         let uu____9058 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9058))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9084 = FStar_List.tl stack1 in
                           norm cfg env uu____9084 tm
                       | uu____9085 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9094;
                             FStar_Syntax_Syntax.pos = uu____9095;
                             FStar_Syntax_Syntax.vars = uu____9096;_},uu____9097,uu____9098))::uu____9099
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9105 -> false in
                    if should_reify
                    then
                      let uu____9106 = FStar_List.tl stack1 in
                      let uu____9107 =
                        let uu____9108 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9108 in
                      norm cfg env uu____9106 uu____9107
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9111 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9111
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_9117 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_9117.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_9117.primitive_steps)
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
                | uu____9119 ->
                    (match stack1 with
                     | uu____9120::uu____9121 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9125)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____9140 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9150 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9150
                           | uu____9157 -> m in
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
              let uu____9169 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9169 with
              | (uu____9170,return_repr) ->
                  let return_inst =
                    let uu____9177 =
                      let uu____9178 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9178.FStar_Syntax_Syntax.n in
                    match uu____9177 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9184::[])
                        ->
                        let uu____9190 =
                          let uu____9193 =
                            let uu____9194 =
                              let uu____9199 =
                                let uu____9201 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9201] in
                              (return_tm, uu____9199) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9194 in
                          FStar_Syntax_Syntax.mk uu____9193 in
                        uu____9190 None e.FStar_Syntax_Syntax.pos
                    | uu____9213 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9216 =
                    let uu____9219 =
                      let uu____9220 =
                        let uu____9230 =
                          let uu____9232 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9233 =
                            let uu____9235 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9235] in
                          uu____9232 :: uu____9233 in
                        (return_inst, uu____9230) in
                      FStar_Syntax_Syntax.Tm_app uu____9220 in
                    FStar_Syntax_Syntax.mk uu____9219 in
                  uu____9216 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9248 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9248 with
               | None  ->
                   let uu____9250 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9250
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9251;
                     FStar_TypeChecker_Env.mtarget = uu____9252;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9253;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9264;
                     FStar_TypeChecker_Env.mtarget = uu____9265;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9266;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9284 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9284)
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
                (fun uu____9314  ->
                   match uu____9314 with
                   | (a,imp) ->
                       let uu____9321 = norm cfg env [] a in
                       (uu____9321, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9336 = comp1 in
            let uu____9339 =
              let uu____9340 =
                let uu____9346 = norm cfg env [] t in
                let uu____9347 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9346, uu____9347) in
              FStar_Syntax_Syntax.Total uu____9340 in
            {
              FStar_Syntax_Syntax.n = uu____9339;
              FStar_Syntax_Syntax.tk = (uu___178_9336.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9336.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9336.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9362 = comp1 in
            let uu____9365 =
              let uu____9366 =
                let uu____9372 = norm cfg env [] t in
                let uu____9373 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9372, uu____9373) in
              FStar_Syntax_Syntax.GTotal uu____9366 in
            {
              FStar_Syntax_Syntax.n = uu____9365;
              FStar_Syntax_Syntax.tk = (uu___179_9362.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9362.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9362.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9404  ->
                      match uu____9404 with
                      | (a,i) ->
                          let uu____9411 = norm cfg env [] a in
                          (uu____9411, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9416  ->
                      match uu___143_9416 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9420 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9420
                      | f -> f)) in
            let uu___180_9424 = comp1 in
            let uu____9427 =
              let uu____9428 =
                let uu___181_9429 = ct in
                let uu____9430 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9431 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9434 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9430;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9429.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9431;
                  FStar_Syntax_Syntax.effect_args = uu____9434;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9428 in
            {
              FStar_Syntax_Syntax.n = uu____9427;
              FStar_Syntax_Syntax.tk = (uu___180_9424.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9424.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9424.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9451 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9451.tcenv);
               delta_level = (uu___182_9451.delta_level);
               primitive_steps = (uu___182_9451.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9456 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9456 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9459 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9473 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9473.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9473.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9473.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9483 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9483
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9488 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9488.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9488.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9488.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9488.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9490 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9490.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9490.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9490.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9490.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9491 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9491.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9491.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9491.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9497 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9500  ->
        match uu____9500 with
        | (x,imp) ->
            let uu____9503 =
              let uu___187_9504 = x in
              let uu____9505 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9504.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9504.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9505
              } in
            (uu____9503, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9511 =
          FStar_List.fold_left
            (fun uu____9518  ->
               fun b  ->
                 match uu____9518 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9511 with | (nbs,uu____9535) -> FStar_List.rev nbs
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
            let uu____9552 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9552
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9557 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9557
               then
                 let uu____9561 =
                   let uu____9564 =
                     let uu____9565 =
                       let uu____9568 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9568 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9565 in
                   FStar_Util.Inl uu____9564 in
                 Some uu____9561
               else
                 (let uu____9572 =
                    let uu____9575 =
                      let uu____9576 =
                        let uu____9579 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9579 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9576 in
                    FStar_Util.Inl uu____9575 in
                  Some uu____9572))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9592 -> lopt
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
              ((let uu____9604 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9604
                then
                  let uu____9605 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9606 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9605
                    uu____9606
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9617 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9617.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9637  ->
                    let uu____9638 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9638);
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
              let uu____9675 =
                let uu___189_9676 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9676.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9676.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9676.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9675
          | (Arg (Univ uu____9681,uu____9682,uu____9683))::uu____9684 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9686,uu____9687))::uu____9688 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9700),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9716  ->
                    let uu____9717 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9717);
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
                 (let uu____9728 = FStar_ST.read m in
                  match uu____9728 with
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
                  | Some (uu____9754,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9776 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9776
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9783  ->
                    let uu____9784 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9784);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9789 =
                  log cfg
                    (fun uu____9791  ->
                       let uu____9792 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9793 =
                         let uu____9794 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9801  ->
                                   match uu____9801 with
                                   | (p,uu____9807,uu____9808) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9794
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9792 uu____9793);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9818  ->
                               match uu___144_9818 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9819 -> false)) in
                     let steps' =
                       let uu____9822 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9822
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9825 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9825.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9825.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9859 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9875 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9909  ->
                                   fun uu____9910  ->
                                     match (uu____9909, uu____9910) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9975 = norm_pat env3 p1 in
                                         (match uu____9975 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9875 with
                          | (pats1,env3) ->
                              ((let uu___191_10041 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_10041.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_10041.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_10055 = x in
                           let uu____10056 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_10055.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_10055.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10056
                           } in
                         ((let uu___193_10062 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_10062.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_10062.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_10067 = x in
                           let uu____10068 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_10067.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_10067.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10068
                           } in
                         ((let uu___195_10074 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_10074.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_10074.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_10084 = x in
                           let uu____10085 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_10084.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_10084.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10085
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_10092 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_10092.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_10092.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10096 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10099 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10099 with
                                 | (p,wopt,e) ->
                                     let uu____10117 = norm_pat env1 p in
                                     (match uu____10117 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10141 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10141 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10146 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10146) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10156) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10161 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10162;
                        FStar_Syntax_Syntax.fv_delta = uu____10163;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10167;
                        FStar_Syntax_Syntax.fv_delta = uu____10168;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10169);_}
                      -> true
                  | uu____10176 -> false in
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
                  let uu____10275 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10275 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10307 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10309 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10311 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10323 ->
                                let uu____10324 =
                                  let uu____10325 = is_cons head1 in
                                  Prims.op_Negation uu____10325 in
                                FStar_Util.Inr uu____10324)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10339 =
                             let uu____10340 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10340.FStar_Syntax_Syntax.n in
                           (match uu____10339 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10347 ->
                                let uu____10348 =
                                  let uu____10349 = is_cons head1 in
                                  Prims.op_Negation uu____10349 in
                                FStar_Util.Inr uu____10348))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10383)::rest_a,(p1,uu____10386)::rest_p) ->
                      let uu____10414 = matches_pat t1 p1 in
                      (match uu____10414 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10428 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10499 = matches_pat scrutinee1 p1 in
                      (match uu____10499 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10509  ->
                                 let uu____10510 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10511 =
                                   let uu____10512 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10512
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10510 uu____10511);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10521 =
                                        let uu____10522 =
                                          let uu____10532 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10532, false) in
                                        Clos uu____10522 in
                                      uu____10521 :: env2) env1 s in
                             let uu____10555 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10555))) in
                let uu____10556 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10556
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10570  ->
                match uu___145_10570 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10573 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10577 -> d in
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
            let uu___198_10597 = config s e in
            {
              steps = (uu___198_10597.steps);
              tcenv = (uu___198_10597.tcenv);
              delta_level = (uu___198_10597.delta_level);
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
      fun t  -> let uu____10616 = config s e in norm_comp uu____10616 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10623 = config [] env in norm_universe uu____10623 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10630 = config [] env in ghost_to_pure_aux uu____10630 [] c
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
        let uu____10642 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10642 in
      let uu____10643 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10643
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10645 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10645.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10645.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10646  ->
                    let uu____10647 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10647))
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
            ((let uu____10660 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10660);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10669 = config [AllowUnboundUniverses] env in
          norm_comp uu____10669 [] c
        with
        | e ->
            ((let uu____10673 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10673);
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
                   let uu____10710 =
                     let uu____10711 =
                       let uu____10716 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10716) in
                     FStar_Syntax_Syntax.Tm_refine uu____10711 in
                   mk uu____10710 t01.FStar_Syntax_Syntax.pos
               | uu____10721 -> t2)
          | uu____10722 -> t2 in
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
        let uu____10744 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10744 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10760 ->
                 let uu____10764 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10764 with
                  | (actuals,uu____10775,uu____10776) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10802 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10802 with
                         | (binders,args) ->
                             let uu____10812 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10815 =
                               let uu____10822 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_54  -> FStar_Util.Inl _0_54) in
                               FStar_All.pipe_right uu____10822
                                 (fun _0_55  -> Some _0_55) in
                             FStar_Syntax_Util.abs binders uu____10812
                               uu____10815)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10858 =
        let uu____10862 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10862, (t.FStar_Syntax_Syntax.n)) in
      match uu____10858 with
      | (Some sort,uu____10869) ->
          let uu____10871 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10871
      | (uu____10872,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10876 ->
          let uu____10880 = FStar_Syntax_Util.head_and_args t in
          (match uu____10880 with
           | (head1,args) ->
               let uu____10906 =
                 let uu____10907 = FStar_Syntax_Subst.compress head1 in
                 uu____10907.FStar_Syntax_Syntax.n in
               (match uu____10906 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10910,thead) ->
                    let uu____10924 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10924 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10959 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_10963 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_10963.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_10963.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_10963.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_10963.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_10963.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_10963.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_10963.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_10963.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_10963.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_10963.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_10963.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_10963.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_10963.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_10963.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_10963.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_10963.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_10963.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_10963.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_10963.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_10963.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_10963.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_10963.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___204_10963.FStar_TypeChecker_Env.synth)
                                 }) t in
                            match uu____10959 with
                            | (uu____10964,ty,uu____10966) ->
                                eta_expand_with_type env t ty))
                | uu____10967 ->
                    let uu____10968 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_10972 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_10972.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_10972.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_10972.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_10972.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_10972.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_10972.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_10972.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_10972.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_10972.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_10972.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_10972.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_10972.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_10972.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_10972.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_10972.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_10972.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_10972.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_10972.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_10972.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_10972.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_10972.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_10972.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___205_10972.FStar_TypeChecker_Env.synth)
                         }) t in
                    (match uu____10968 with
                     | (uu____10973,ty,uu____10975) ->
                         eta_expand_with_type env t ty)))