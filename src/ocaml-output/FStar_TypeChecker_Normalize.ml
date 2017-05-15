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
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____66 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____70 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____74 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____78 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____82 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____86 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____90 -> false
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
    match projectee with | Clos _0 -> true | uu____165 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____204 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____215 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___137_219  ->
    match uu___137_219 with
    | Clos (uu____220,t,uu____222,uu____223) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____234 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____347 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____371 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____395 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____422 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____451 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either Prims.option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____490 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____513 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____535 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____564 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____591 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____603 =
      let uu____604 = FStar_Syntax_Util.un_uinst t in
      uu____604.FStar_Syntax_Syntax.n in
    match uu____603 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_refl_embed_lid
    | uu____608 -> false
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____648 = FStar_ST.read r in
  match uu____648 with
  | Some uu____653 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____662 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____662 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___138_667  ->
    match uu___138_667 with
    | Arg (c,uu____669,uu____670) ->
        let uu____671 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____671
    | MemoLazy uu____672 -> "MemoLazy"
    | Abs (uu____676,bs,uu____678,uu____679,uu____680) ->
        let uu____687 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____687
    | UnivArgs uu____692 -> "UnivArgs"
    | Match uu____696 -> "Match"
    | App (t,uu____701,uu____702) ->
        let uu____703 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____703
    | Meta (m,uu____705) -> "Meta"
    | Let uu____706 -> "Let"
    | Steps (uu____711,uu____712,uu____713) -> "Steps"
    | Debug t ->
        let uu____719 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____719
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____725 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____725 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____739 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____739 then f () else ()
let is_empty uu___139_748 =
  match uu___139_748 with | [] -> true | uu____750 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____768 ->
      let uu____769 =
        let uu____770 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____770 in
      failwith uu____769
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
          let uu____801 =
            FStar_List.fold_left
              (fun uu____810  ->
                 fun u1  ->
                   match uu____810 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____825 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____825 with
                        | (k_u,n1) ->
                            let uu____834 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____834
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____801 with
          | (uu____844,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____860 = FStar_List.nth env x in
                 match uu____860 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____863 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____867 ->
                   let uu____868 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____868
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____878 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____878 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____889 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____889 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____894 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____897 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____897 with
                                  | (uu____900,m) -> n1 <= m)) in
                        if uu____894 then rest1 else us1
                    | uu____904 -> us1)
               | uu____907 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____910 = aux u3 in
              FStar_List.map (fun _0_29  -> FStar_Syntax_Syntax.U_succ _0_29)
                uu____910 in
        let uu____912 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____912
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____914 = aux u in
           match uu____914 with
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
          (fun uu____1011  ->
             let uu____1012 = FStar_Syntax_Print.tag_of_term t in
             let uu____1013 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1012
               uu____1013);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1014 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1017 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1041 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1051 =
                    let uu____1052 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1052 in
                  mk uu____1051 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1059 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1059
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1061 = lookup_bvar env x in
                  (match uu____1061 with
                   | Univ uu____1062 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1066) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1134 = closures_as_binders_delayed cfg env bs in
                  (match uu____1134 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1154 =
                         let uu____1155 =
                           let uu____1170 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1170) in
                         FStar_Syntax_Syntax.Tm_abs uu____1155 in
                       mk uu____1154 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1200 = closures_as_binders_delayed cfg env bs in
                  (match uu____1200 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1231 =
                    let uu____1238 =
                      let uu____1242 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1242] in
                    closures_as_binders_delayed cfg env uu____1238 in
                  (match uu____1231 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1256 =
                         let uu____1257 =
                           let uu____1262 =
                             let uu____1263 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1263 Prims.fst in
                           (uu____1262, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1257 in
                       mk uu____1256 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1331 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1331
                    | FStar_Util.Inr c ->
                        let uu____1345 = close_comp cfg env c in
                        FStar_Util.Inr uu____1345 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1360 =
                    let uu____1361 =
                      let uu____1379 = closure_as_term_delayed cfg env t11 in
                      (uu____1379, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1361 in
                  mk uu____1360 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1417 =
                    let uu____1418 =
                      let uu____1423 = closure_as_term_delayed cfg env t' in
                      let uu____1426 =
                        let uu____1427 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1427 in
                      (uu____1423, uu____1426) in
                    FStar_Syntax_Syntax.Tm_meta uu____1418 in
                  mk uu____1417 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1469 =
                    let uu____1470 =
                      let uu____1475 = closure_as_term_delayed cfg env t' in
                      let uu____1478 =
                        let uu____1479 =
                          let uu____1484 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1484) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1479 in
                      (uu____1475, uu____1478) in
                    FStar_Syntax_Syntax.Tm_meta uu____1470 in
                  mk uu____1469 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1503 =
                    let uu____1504 =
                      let uu____1509 = closure_as_term_delayed cfg env t' in
                      let uu____1512 =
                        let uu____1513 =
                          let uu____1519 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1519) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1513 in
                      (uu____1509, uu____1512) in
                    FStar_Syntax_Syntax.Tm_meta uu____1504 in
                  mk uu____1503 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1532 =
                    let uu____1533 =
                      let uu____1538 = closure_as_term_delayed cfg env t' in
                      (uu____1538, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1533 in
                  mk uu____1532 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1559  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1570 -> body
                    | FStar_Util.Inl uu____1571 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___152_1573 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___152_1573.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___152_1573.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___152_1573.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1580,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1604  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1609 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1609
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1613  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___153_1616 = lb in
                    let uu____1617 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1620 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___153_1616.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___153_1616.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1617;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___153_1616.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1620
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1631  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1686 =
                    match uu____1686 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1732 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                              let uu____1752 = norm_pat env2 hd1 in
                              (match uu____1752 with
                               | (hd2,env') ->
                                   let tl2 =
                                     FStar_All.pipe_right tl1
                                       (FStar_List.map
                                          (fun p1  ->
                                             let uu____1788 =
                                               norm_pat env2 p1 in
                                             Prims.fst uu____1788)) in
                                   ((let uu___154_1800 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___154_1800.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___154_1800.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1817 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1851  ->
                                        fun uu____1852  ->
                                          match (uu____1851, uu____1852) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1917 =
                                                norm_pat env3 p1 in
                                              (match uu____1917 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1817 with
                               | (pats1,env3) ->
                                   ((let uu___155_1983 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___155_1983.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___155_1983.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___156_1997 = x in
                                let uu____1998 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_1997.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_1997.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1998
                                } in
                              ((let uu___157_2004 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___157_2004.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_2004.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___158_2009 = x in
                                let uu____2010 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___158_2009.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___158_2009.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2010
                                } in
                              ((let uu___159_2016 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___159_2016.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___159_2016.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___160_2026 = x in
                                let uu____2027 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_2026.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_2026.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2027
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___161_2034 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___161_2034.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_2034.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2037 = norm_pat env1 pat in
                        (match uu____2037 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2061 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2061 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2066 =
                    let uu____2067 =
                      let uu____2083 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2083) in
                    FStar_Syntax_Syntax.Tm_match uu____2067 in
                  mk uu____2066 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2136 -> closure_as_term cfg env t
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
        | uu____2152 ->
            FStar_List.map
              (fun uu____2162  ->
                 match uu____2162 with
                 | (x,imp) ->
                     let uu____2177 = closure_as_term_delayed cfg env x in
                     (uu____2177, imp)) args
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
        let uu____2189 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2213  ->
                  fun uu____2214  ->
                    match (uu____2213, uu____2214) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___162_2258 = b in
                          let uu____2259 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___162_2258.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___162_2258.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2259
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2189 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2306 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2318 = closure_as_term_delayed cfg env t in
                 let uu____2319 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2318 uu____2319
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2329 = closure_as_term_delayed cfg env t in
                 let uu____2330 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2329 uu____2330
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
                        (fun uu___140_2346  ->
                           match uu___140_2346 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2350 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2350
                           | f -> f)) in
                 let uu____2354 =
                   let uu___163_2355 = c1 in
                   let uu____2356 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2356;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___163_2355.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2354)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___141_2360  ->
            match uu___141_2360 with
            | FStar_Syntax_Syntax.DECREASES uu____2361 -> false
            | uu____2364 -> true))
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
            let uu____2392 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2392
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2409 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2409
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2435 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2459 =
      let uu____2460 =
        let uu____2466 = FStar_Util.string_of_int i in (uu____2466, None) in
      FStar_Const.Const_int uu____2460 in
    const_as_tm uu____2459 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2493 =
    match uu____2493 with
    | (a,uu____2498) ->
        let uu____2500 =
          let uu____2501 = FStar_Syntax_Subst.compress a in
          uu____2501.FStar_Syntax_Syntax.n in
        (match uu____2500 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2511 = FStar_Util.int_of_string i in Some uu____2511
         | uu____2512 -> None) in
  let arg_as_bounded_int uu____2521 =
    match uu____2521 with
    | (a,uu____2528) ->
        let uu____2532 =
          let uu____2533 = FStar_Syntax_Subst.compress a in
          uu____2533.FStar_Syntax_Syntax.n in
        (match uu____2532 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2540;
                FStar_Syntax_Syntax.pos = uu____2541;
                FStar_Syntax_Syntax.vars = uu____2542;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2544;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2545;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2546;_},uu____2547)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2578 =
               let uu____2581 = FStar_Util.int_of_string i in
               (fv1, uu____2581) in
             Some uu____2578
         | uu____2584 -> None) in
  let arg_as_bool uu____2593 =
    match uu____2593 with
    | (a,uu____2598) ->
        let uu____2600 =
          let uu____2601 = FStar_Syntax_Subst.compress a in
          uu____2601.FStar_Syntax_Syntax.n in
        (match uu____2600 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2606 -> None) in
  let arg_as_char uu____2613 =
    match uu____2613 with
    | (a,uu____2618) ->
        let uu____2620 =
          let uu____2621 = FStar_Syntax_Subst.compress a in
          uu____2621.FStar_Syntax_Syntax.n in
        (match uu____2620 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2626 -> None) in
  let arg_as_string uu____2633 =
    match uu____2633 with
    | (a,uu____2638) ->
        let uu____2640 =
          let uu____2641 = FStar_Syntax_Subst.compress a in
          uu____2641.FStar_Syntax_Syntax.n in
        (match uu____2640 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2646)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2649 -> None) in
  let arg_as_list f uu____2670 =
    match uu____2670 with
    | (a,uu____2679) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2698 -> None
          | (Some x)::xs ->
              let uu____2708 = sequence xs in
              (match uu____2708 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2719 = FStar_Syntax_Util.list_elements a in
        (match uu____2719 with
         | None  -> None
         | Some elts ->
             let uu____2729 =
               FStar_List.map
                 (fun x  ->
                    let uu____2734 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2734) elts in
             sequence uu____2729) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2764 = f a in Some uu____2764
    | uu____2765 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2804 = f a0 a1 in Some uu____2804
    | uu____2805 -> None in
  let unary_op as_a f r args =
    let uu____2849 = FStar_List.map as_a args in lift_unary (f r) uu____2849 in
  let binary_op as_a f r args =
    let uu____2899 = FStar_List.map as_a args in lift_binary (f r) uu____2899 in
  let as_primitive_step uu____2916 =
    match uu____2916 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2954 = f x in int_as_const r uu____2954) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2977 = f x y in int_as_const r uu____2977) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2994 = f x in bool_as_const r uu____2994) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3017 = f x y in bool_as_const r uu____3017) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3040 = f x y in string_as_const r uu____3040) in
  let list_of_string' rng s =
    let name l =
      let uu____3054 =
        let uu____3055 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3055 in
      mk uu____3054 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3065 =
      let uu____3067 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3067 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3065 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_of_int1 rng i =
    let uu____3100 = FStar_Util.string_of_int i in
    string_as_const rng uu____3100 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3116 = FStar_Util.string_of_int i in
    string_as_const rng uu____3116 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3135 =
      let uu____3145 =
        let uu____3155 =
          let uu____3165 =
            let uu____3175 =
              let uu____3185 =
                let uu____3195 =
                  let uu____3205 =
                    let uu____3215 =
                      let uu____3225 =
                        let uu____3235 =
                          let uu____3245 =
                            let uu____3255 =
                              let uu____3265 =
                                let uu____3275 =
                                  let uu____3285 =
                                    let uu____3295 =
                                      let uu____3305 =
                                        let uu____3314 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3314, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3320 =
                                        let uu____3330 =
                                          let uu____3339 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3339, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        [uu____3330] in
                                      uu____3305 :: uu____3320 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3295 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3285 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3275 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3265 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3255 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3245 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3235 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3225 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3215 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3205 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3195 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3185 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3175 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3165 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3155 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3145 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3135 in
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
      let uu____3647 =
        let uu____3648 =
          let uu____3649 = FStar_Syntax_Syntax.as_arg c in [uu____3649] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3648 in
      uu____3647 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3673 =
              let uu____3682 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3682, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3691  ->
                        fun uu____3692  ->
                          match (uu____3691, uu____3692) with
                          | ((int_to_t1,x),(uu____3703,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3709 =
              let uu____3719 =
                let uu____3728 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3728, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3737  ->
                          fun uu____3738  ->
                            match (uu____3737, uu____3738) with
                            | ((int_to_t1,x),(uu____3749,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3755 =
                let uu____3765 =
                  let uu____3774 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3774, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3783  ->
                            fun uu____3784  ->
                              match (uu____3783, uu____3784) with
                              | ((int_to_t1,x),(uu____3795,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3765] in
              uu____3719 :: uu____3755 in
            uu____3673 :: uu____3709)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3861)::(a1,uu____3863)::(a2,uu____3865)::[] ->
        let uu____3894 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3894 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3896 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3896
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3901 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3901
         | uu____3906 -> None)
    | uu____3907 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,_)::(a1,_)::(a2,_)::[]|(_typ,_)::_::(a1,_)::(a2,_)::[] ->
        let uu____3989 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3989 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___164_3993 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___164_3993.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___164_3993.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___164_3993.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___165_4000 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_4000.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_4000.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_4000.FStar_Syntax_Syntax.vars)
                })
         | uu____4005 -> None)
    | uu____4006 -> failwith "Unexpected number of arguments" in
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
      let uu____4017 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4017
      then tm
      else
        (let uu____4019 = FStar_Syntax_Util.head_and_args tm in
         match uu____4019 with
         | (head1,args) ->
             let uu____4045 =
               let uu____4046 = FStar_Syntax_Util.un_uinst head1 in
               uu____4046.FStar_Syntax_Syntax.n in
             (match uu____4045 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4050 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4050 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4062 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4062 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4065 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___166_4072 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___166_4072.tcenv);
           delta_level = (uu___166_4072.delta_level);
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
        let uu___167_4094 = t in
        {
          FStar_Syntax_Syntax.n = (uu___167_4094.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___167_4094.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___167_4094.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4113 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____4140 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4140
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
             let uu____4180 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4180
             then
               let uu____4181 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4181 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4347 -> tm)
             else
               (let uu____4357 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4357
                then
                  let uu____4358 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4358 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____4524 -> tm
                else
                  (let uu____4534 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4534
                   then
                     let uu____4535 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4535 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4624)::(uu____4625,(arg,uu____4627))::[]
                         -> arg
                     | uu____4668 -> tm
                   else
                     (let uu____4678 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4678
                      then
                        let uu____4679 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4679 with
                        | (Some (true ),uu____4712)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4736)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4760 -> tm
                      else
                        (let uu____4770 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid) in
                         if uu____4770
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____4811 =
                                 let uu____4812 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4812.FStar_Syntax_Syntax.n in
                               (match uu____4811 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4815::[],body,uu____4817) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____4843 -> tm)
                                | uu____4845 -> tm)
                           | uu____4846 -> tm
                         else reduce_equality cfg tm))))
         | uu____4853 -> tm)
let is_norm_request hd1 args =
  let uu____4868 =
    let uu____4872 =
      let uu____4873 = FStar_Syntax_Util.un_uinst hd1 in
      uu____4873.FStar_Syntax_Syntax.n in
    (uu____4872, args) in
  match uu____4868 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4878::uu____4879::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4882::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4884 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____4917 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___142_4924  ->
    match uu___142_4924 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____4926;
           FStar_Syntax_Syntax.pos = uu____4927;
           FStar_Syntax_Syntax.vars = uu____4928;_},uu____4929,uu____4930))::uu____4931
        -> true
    | uu____4937 -> false
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
            (fun uu____5052  ->
               let uu____5053 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____5054 = FStar_Syntax_Print.term_to_string t1 in
               let uu____5055 =
                 let uu____5056 =
                   let uu____5058 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left Prims.fst uu____5058 in
                 stack_to_string uu____5056 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____5053
                 uu____5054 uu____5055);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____5070 ->
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
                 let uu___168_5127 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___168_5127.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___168_5127.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___168_5127.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____5153 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____5153) && (is_norm_request hd1 args))
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
                 let uu___169_5166 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___169_5166.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___169_5166.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____5171;
                  FStar_Syntax_Syntax.pos = uu____5172;
                  FStar_Syntax_Syntax.vars = uu____5173;_},a1::a2::rest)
               ->
               let uu____5207 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5207 with
                | (hd1,uu____5218) ->
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
                    (FStar_Const.Const_reflect uu____5273);
                  FStar_Syntax_Syntax.tk = uu____5274;
                  FStar_Syntax_Syntax.pos = uu____5275;
                  FStar_Syntax_Syntax.vars = uu____5276;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____5299 = FStar_List.tl stack1 in
               norm cfg env uu____5299 (Prims.fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____5302;
                  FStar_Syntax_Syntax.pos = uu____5303;
                  FStar_Syntax_Syntax.vars = uu____5304;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____5327 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____5327 with
                | (reify_head,uu____5338) ->
                    let a1 =
                      let uu____5354 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____5354 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____5357);
                            FStar_Syntax_Syntax.tk = uu____5358;
                            FStar_Syntax_Syntax.pos = uu____5359;
                            FStar_Syntax_Syntax.vars = uu____5360;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____5385 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____5393 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____5393
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____5400 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____5400
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____5403 =
                      let uu____5407 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____5407, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____5403 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___143_5416  ->
                         match uu___143_5416 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               if Prims.op_Negation should_delta
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____5420 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____5420 in
                  let uu____5421 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____5421 with
                  | None  ->
                      (log cfg
                         (fun uu____5432  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____5438  ->
                            let uu____5439 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____5440 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____5439 uu____5440);
                       (let n1 = FStar_List.length us in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____5447))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t2
                          | uu____5460 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____5461 ->
                              let uu____5462 =
                                let uu____5463 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____5463 in
                              failwith uu____5462
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____5470 = lookup_bvar env x in
               (match uu____5470 with
                | Univ uu____5471 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____5486 = FStar_ST.read r in
                      (match uu____5486 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____5505  ->
                                 let uu____5506 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____5507 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____5506
                                   uu____5507);
                            (let uu____5508 =
                               let uu____5509 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____5509.FStar_Syntax_Syntax.n in
                             match uu____5508 with
                             | FStar_Syntax_Syntax.Tm_abs uu____5512 ->
                                 norm cfg env2 stack1 t'
                             | uu____5527 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____5560)::uu____5561 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____5566)::uu____5567 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____5573,uu____5574))::stack_rest ->
                    (match c with
                     | Univ uu____5577 -> norm cfg (c :: env) stack_rest t1
                     | uu____5578 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____5581::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____5594  ->
                                         let uu____5595 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5595);
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
                                           (fun uu___144_5609  ->
                                              match uu___144_5609 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____5610 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____5612  ->
                                         let uu____5613 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5613);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____5624  ->
                                         let uu____5625 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____5625);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____5626 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____5633 ->
                                   let cfg1 =
                                     let uu___170_5641 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___170_5641.tcenv);
                                       delta_level =
                                         (uu___170_5641.delta_level);
                                       primitive_steps =
                                         (uu___170_5641.primitive_steps)
                                     } in
                                   let uu____5642 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____5642)
                          | uu____5643::tl1 ->
                              (log cfg
                                 (fun uu____5653  ->
                                    let uu____5654 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____5654);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___171_5678 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___171_5678.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____5691  ->
                          let uu____5692 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5692);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____5703 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5703
                    else
                      (let uu____5705 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____5705 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____5734 =
                                   let uu____5740 =
                                     let uu____5741 =
                                       let uu____5742 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____5742 in
                                     FStar_All.pipe_right uu____5741
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____5740
                                     (fun _0_30  -> FStar_Util.Inl _0_30) in
                                 FStar_All.pipe_right uu____5734
                                   (fun _0_31  -> Some _0_31)
                             | uu____5767 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____5781  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____5786  ->
                                 let uu____5787 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____5787);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___172_5797 = cfg in
                               let uu____5798 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___172_5797.steps);
                                 tcenv = (uu___172_5797.tcenv);
                                 delta_level = (uu___172_5797.delta_level);
                                 primitive_steps = uu____5798
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
                      (fun uu____5830  ->
                         fun stack2  ->
                           match uu____5830 with
                           | (a,aq) ->
                               let uu____5838 =
                                 let uu____5839 =
                                   let uu____5843 =
                                     let uu____5844 =
                                       let uu____5854 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5854, false) in
                                     Clos uu____5844 in
                                   (uu____5843, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5839 in
                               uu____5838 :: stack2) args) in
               (log cfg
                  (fun uu____5876  ->
                     let uu____5877 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5877);
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
                             ((let uu___173_5898 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___173_5898.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___173_5898.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____5899 ->
                      let uu____5902 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____5902)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____5905 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____5905 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____5921 =
                          let uu____5922 =
                            let uu____5927 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___174_5928 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___174_5928.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___174_5928.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____5927) in
                          FStar_Syntax_Syntax.Tm_refine uu____5922 in
                        mk uu____5921 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____5941 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____5941
               else
                 (let uu____5943 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____5943 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____5949 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____5955  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____5949 c1 in
                      let t2 =
                        let uu____5962 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____5962 c2 in
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
                | uu____6019 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____6022  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____6035 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____6035
                        | FStar_Util.Inr c ->
                            let uu____6043 = norm_comp cfg env c in
                            FStar_Util.Inr uu____6043 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____6048 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____6048)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____6099,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____6100;
                              FStar_Syntax_Syntax.lbunivs = uu____6101;
                              FStar_Syntax_Syntax.lbtyp = uu____6102;
                              FStar_Syntax_Syntax.lbeff = uu____6103;
                              FStar_Syntax_Syntax.lbdef = uu____6104;_}::uu____6105),uu____6106)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____6132 =
                 (let uu____6133 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____6133) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____6134 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____6134))) in
               if uu____6132
               then
                 let env1 =
                   let uu____6137 =
                     let uu____6138 =
                       let uu____6148 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____6148,
                         false) in
                     Clos uu____6138 in
                   uu____6137 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____6172 =
                    let uu____6175 =
                      let uu____6176 =
                        let uu____6177 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____6177
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____6176] in
                    FStar_Syntax_Subst.open_term uu____6175 body in
                  match uu____6172 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___175_6183 = lb in
                        let uu____6184 =
                          let uu____6187 =
                            let uu____6188 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____6188 Prims.fst in
                          FStar_All.pipe_right uu____6187
                            (fun _0_32  -> FStar_Util.Inl _0_32) in
                        let uu____6197 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____6200 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____6184;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___175_6183.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6197;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___175_6183.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6200
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____6210  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____6226 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____6226
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____6239 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____6261  ->
                        match uu____6261 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____6300 =
                                let uu___176_6301 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___176_6301.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___176_6301.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____6300 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____6239 with
                | (rec_env,memos,uu____6361) ->
                    let uu____6376 =
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
                             let uu____6418 =
                               let uu____6419 =
                                 let uu____6429 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____6429, false) in
                               Clos uu____6419 in
                             uu____6418 :: env1) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____6467;
                             FStar_Syntax_Syntax.pos = uu____6468;
                             FStar_Syntax_Syntax.vars = uu____6469;_},uu____6470,uu____6471))::uu____6472
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6478 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____6485 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____6485
                        then
                          let uu___177_6486 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___177_6486.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___177_6486.primitive_steps)
                          }
                        else
                          (let uu___178_6488 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___178_6488.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___178_6488.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____6490 =
                         let uu____6491 = FStar_Syntax_Subst.compress head1 in
                         uu____6491.FStar_Syntax_Syntax.n in
                       match uu____6490 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6505 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6505 with
                            | (uu____6506,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____6510 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____6517 =
                                         let uu____6518 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____6518.FStar_Syntax_Syntax.n in
                                       match uu____6517 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____6523,uu____6524))
                                           ->
                                           let uu____6533 =
                                             let uu____6534 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____6534.FStar_Syntax_Syntax.n in
                                           (match uu____6533 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____6539,msrc,uu____6541))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____6550 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____6550
                                            | uu____6551 -> None)
                                       | uu____6552 -> None in
                                     let uu____6553 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____6553 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___179_6557 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___179_6557.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___179_6557.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___179_6557.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____6558 =
                                            FStar_List.tl stack1 in
                                          let uu____6559 =
                                            let uu____6560 =
                                              let uu____6563 =
                                                let uu____6564 =
                                                  let uu____6572 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____6572) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____6564 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6563 in
                                            uu____6560 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____6558 uu____6559
                                      | None  ->
                                          let uu____6589 =
                                            let uu____6590 = is_return body in
                                            match uu____6590 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6593;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6594;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6595;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____6600 -> false in
                                          if uu____6589
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
                                               let uu____6620 =
                                                 let uu____6623 =
                                                   let uu____6624 =
                                                     let uu____6639 =
                                                       let uu____6641 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6641] in
                                                     (uu____6639, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____6624 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6623 in
                                               uu____6620 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____6674 =
                                                 let uu____6675 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____6675.FStar_Syntax_Syntax.n in
                                               match uu____6674 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____6681::uu____6682::[])
                                                   ->
                                                   let uu____6688 =
                                                     let uu____6691 =
                                                       let uu____6692 =
                                                         let uu____6697 =
                                                           let uu____6699 =
                                                             let uu____6700 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____6700 in
                                                           let uu____6701 =
                                                             let uu____6703 =
                                                               let uu____6704
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____6704 in
                                                             [uu____6703] in
                                                           uu____6699 ::
                                                             uu____6701 in
                                                         (bind1, uu____6697) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____6692 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____6691 in
                                                   uu____6688 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____6716 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____6722 =
                                                 let uu____6725 =
                                                   let uu____6726 =
                                                     let uu____6736 =
                                                       let uu____6738 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____6739 =
                                                         let uu____6741 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____6742 =
                                                           let uu____6744 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____6745 =
                                                             let uu____6747 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____6748 =
                                                               let uu____6750
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____6751
                                                                 =
                                                                 let uu____6753
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____6753] in
                                                               uu____6750 ::
                                                                 uu____6751 in
                                                             uu____6747 ::
                                                               uu____6748 in
                                                           uu____6744 ::
                                                             uu____6745 in
                                                         uu____6741 ::
                                                           uu____6742 in
                                                       uu____6738 ::
                                                         uu____6739 in
                                                     (bind_inst, uu____6736) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6726 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6725 in
                                               uu____6722 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____6765 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____6765 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____6783 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____6783 with
                            | (uu____6784,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____6807 =
                                        let uu____6808 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____6808.FStar_Syntax_Syntax.n in
                                      match uu____6807 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____6814) -> t4
                                      | uu____6819 -> head2 in
                                    let uu____6820 =
                                      let uu____6821 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____6821.FStar_Syntax_Syntax.n in
                                    match uu____6820 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____6826 -> None in
                                  let uu____6827 = maybe_extract_fv head2 in
                                  match uu____6827 with
                                  | Some x when
                                      let uu____6833 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____6833
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____6837 =
                                          maybe_extract_fv head3 in
                                        match uu____6837 with
                                        | Some uu____6840 -> Some true
                                        | uu____6841 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____6844 -> (head2, None) in
                                ((let is_arg_impure uu____6855 =
                                    match uu____6855 with
                                    | (e,q) ->
                                        let uu____6860 =
                                          let uu____6861 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____6861.FStar_Syntax_Syntax.n in
                                        (match uu____6860 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____6876 -> false) in
                                  let uu____6877 =
                                    let uu____6878 =
                                      let uu____6882 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____6882 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____6878 in
                                  if uu____6877
                                  then
                                    let uu____6885 =
                                      let uu____6886 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____6886 in
                                    failwith uu____6885
                                  else ());
                                 (let uu____6888 =
                                    maybe_unfold_action head_app in
                                  match uu____6888 with
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
                                      let uu____6923 = FStar_List.tl stack1 in
                                      norm cfg env uu____6923 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____6937 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____6937 in
                           let uu____6938 = FStar_List.tl stack1 in
                           norm cfg env uu____6938 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____7021  ->
                                     match uu____7021 with
                                     | (pat,wopt,tm) ->
                                         let uu____7059 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____7059))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____7085 = FStar_List.tl stack1 in
                           norm cfg env uu____7085 tm
                       | uu____7086 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____7095;
                             FStar_Syntax_Syntax.pos = uu____7096;
                             FStar_Syntax_Syntax.vars = uu____7097;_},uu____7098,uu____7099))::uu____7100
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7106 -> false in
                    if should_reify
                    then
                      let uu____7107 = FStar_List.tl stack1 in
                      let uu____7108 =
                        let uu____7109 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____7109 in
                      norm cfg env uu____7107 uu____7108
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____7112 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____7112
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___180_7118 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___180_7118.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___180_7118.primitive_steps)
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
                | uu____7120 ->
                    (match stack1 with
                     | uu____7121::uu____7122 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____7126)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____7141 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____7151 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____7151
                           | uu____7158 -> m in
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
              let uu____7170 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____7170 with
              | (uu____7171,return_repr) ->
                  let return_inst =
                    let uu____7178 =
                      let uu____7179 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____7179.FStar_Syntax_Syntax.n in
                    match uu____7178 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____7185::[])
                        ->
                        let uu____7191 =
                          let uu____7194 =
                            let uu____7195 =
                              let uu____7200 =
                                let uu____7202 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____7202] in
                              (return_tm, uu____7200) in
                            FStar_Syntax_Syntax.Tm_uinst uu____7195 in
                          FStar_Syntax_Syntax.mk uu____7194 in
                        uu____7191 None e.FStar_Syntax_Syntax.pos
                    | uu____7214 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____7217 =
                    let uu____7220 =
                      let uu____7221 =
                        let uu____7231 =
                          let uu____7233 = FStar_Syntax_Syntax.as_arg t in
                          let uu____7234 =
                            let uu____7236 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7236] in
                          uu____7233 :: uu____7234 in
                        (return_inst, uu____7231) in
                      FStar_Syntax_Syntax.Tm_app uu____7221 in
                    FStar_Syntax_Syntax.mk uu____7220 in
                  uu____7217 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____7249 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____7249 with
               | None  ->
                   let uu____7251 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____7251
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7252;
                     FStar_TypeChecker_Env.mtarget = uu____7253;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7254;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____7265;
                     FStar_TypeChecker_Env.mtarget = uu____7266;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____7267;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____7285 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____7285)
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
                (fun uu____7315  ->
                   match uu____7315 with
                   | (a,imp) ->
                       let uu____7322 = norm cfg env [] a in
                       (uu____7322, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___181_7337 = comp1 in
            let uu____7340 =
              let uu____7341 =
                let uu____7347 = norm cfg env [] t in
                let uu____7348 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7347, uu____7348) in
              FStar_Syntax_Syntax.Total uu____7341 in
            {
              FStar_Syntax_Syntax.n = uu____7340;
              FStar_Syntax_Syntax.tk = (uu___181_7337.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___181_7337.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___181_7337.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___182_7363 = comp1 in
            let uu____7366 =
              let uu____7367 =
                let uu____7373 = norm cfg env [] t in
                let uu____7374 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____7373, uu____7374) in
              FStar_Syntax_Syntax.GTotal uu____7367 in
            {
              FStar_Syntax_Syntax.n = uu____7366;
              FStar_Syntax_Syntax.tk = (uu___182_7363.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___182_7363.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___182_7363.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7405  ->
                      match uu____7405 with
                      | (a,i) ->
                          let uu____7412 = norm cfg env [] a in
                          (uu____7412, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___145_7417  ->
                      match uu___145_7417 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____7421 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____7421
                      | f -> f)) in
            let uu___183_7425 = comp1 in
            let uu____7428 =
              let uu____7429 =
                let uu___184_7430 = ct in
                let uu____7431 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____7432 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____7435 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____7431;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___184_7430.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____7432;
                  FStar_Syntax_Syntax.effect_args = uu____7435;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____7429 in
            {
              FStar_Syntax_Syntax.n = uu____7428;
              FStar_Syntax_Syntax.tk = (uu___183_7425.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_7425.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_7425.FStar_Syntax_Syntax.vars)
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
            (let uu___185_7452 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___185_7452.tcenv);
               delta_level = (uu___185_7452.delta_level);
               primitive_steps = (uu___185_7452.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____7457 = norm1 t in
          FStar_Syntax_Util.non_informative uu____7457 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____7460 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___186_7474 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___186_7474.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___186_7474.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_7474.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____7484 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____7484
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___187_7489 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___187_7489.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___187_7489.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___187_7489.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___187_7489.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___188_7491 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___188_7491.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___188_7491.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___188_7491.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___188_7491.FStar_Syntax_Syntax.flags)
                    } in
              let uu___189_7492 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___189_7492.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___189_7492.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___189_7492.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____7498 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____7501  ->
        match uu____7501 with
        | (x,imp) ->
            let uu____7504 =
              let uu___190_7505 = x in
              let uu____7506 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___190_7505.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___190_7505.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____7506
              } in
            (uu____7504, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____7512 =
          FStar_List.fold_left
            (fun uu____7519  ->
               fun b  ->
                 match uu____7519 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____7512 with | (nbs,uu____7536) -> FStar_List.rev nbs
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
            let uu____7553 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____7553
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____7558 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____7558
               then
                 let uu____7562 =
                   let uu____7565 =
                     let uu____7566 =
                       let uu____7569 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____7569 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____7566 in
                   FStar_Util.Inl uu____7565 in
                 Some uu____7562
               else
                 (let uu____7573 =
                    let uu____7576 =
                      let uu____7577 =
                        let uu____7580 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____7580 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____7577 in
                    FStar_Util.Inl uu____7576 in
                  Some uu____7573))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____7593 -> lopt
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
              ((let uu____7605 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____7605
                then
                  let uu____7606 = FStar_Syntax_Print.term_to_string tm in
                  let uu____7607 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____7606
                    uu____7607
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___191_7618 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___191_7618.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____7638  ->
                    let uu____7639 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____7639);
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
              let uu____7676 =
                let uu___192_7677 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___192_7677.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___192_7677.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___192_7677.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____7676
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____7699),aq,r))::stack2 ->
              (log cfg
                 (fun uu____7715  ->
                    let uu____7716 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____7716);
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
                 (let uu____7727 = FStar_ST.read m in
                  match uu____7727 with
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
                  | Some (uu____7753,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____7775 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____7775
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____7782  ->
                    let uu____7783 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____7783);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____7788 =
                  log cfg
                    (fun uu____7790  ->
                       let uu____7791 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____7792 =
                         let uu____7793 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____7800  ->
                                   match uu____7800 with
                                   | (p,uu____7806,uu____7807) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____7793
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____7791 uu____7792);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___146_7817  ->
                               match uu___146_7817 with
                               | FStar_TypeChecker_Env.Inlining 
                                 |FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____7818 -> false)) in
                     let steps' =
                       let uu____7821 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____7821
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___193_7824 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___193_7824.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___193_7824.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____7858 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_disj [] ->
                         failwith "Impossible"
                     | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                         let uu____7878 = norm_pat env2 hd1 in
                         (match uu____7878 with
                          | (hd2,env') ->
                              let tl2 =
                                FStar_All.pipe_right tl1
                                  (FStar_List.map
                                     (fun p1  ->
                                        let uu____7914 = norm_pat env2 p1 in
                                        Prims.fst uu____7914)) in
                              ((let uu___194_7926 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_disj (hd2 ::
                                       tl2));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___194_7926.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___194_7926.FStar_Syntax_Syntax.p)
                                }), env'))
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____7943 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____7977  ->
                                   fun uu____7978  ->
                                     match (uu____7977, uu____7978) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____8043 = norm_pat env3 p1 in
                                         (match uu____8043 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____7943 with
                          | (pats1,env3) ->
                              ((let uu___195_8109 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___195_8109.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___195_8109.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___196_8123 = x in
                           let uu____8124 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_8123.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_8123.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8124
                           } in
                         ((let uu___197_8130 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___197_8130.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_8130.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___198_8135 = x in
                           let uu____8136 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___198_8135.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___198_8135.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8136
                           } in
                         ((let uu___199_8142 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___199_8142.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___199_8142.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___200_8152 = x in
                           let uu____8153 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___200_8152.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___200_8152.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8153
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___201_8160 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___201_8160.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___201_8160.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____8164 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____8167 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____8167 with
                                 | (p,wopt,e) ->
                                     let uu____8185 = norm_pat env1 p in
                                     (match uu____8185 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____8209 =
                                                  norm_or_whnf env2 w in
                                                Some uu____8209 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____8214 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____8214) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____8224) -> is_cons h
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
                  | uu____8235 -> false in
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
                  let uu____8334 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____8334 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1 in
                                  match m with
                                  | FStar_Util.Inl uu____8391 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____8422 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____8434 ->
                                let uu____8435 =
                                  let uu____8436 = is_cons head1 in
                                  Prims.op_Negation uu____8436 in
                                FStar_Util.Inr uu____8435)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____8450 =
                             let uu____8451 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____8451.FStar_Syntax_Syntax.n in
                           (match uu____8450 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____8458 ->
                                let uu____8459 =
                                  let uu____8460 = is_cons head1 in
                                  Prims.op_Negation uu____8460 in
                                FStar_Util.Inr uu____8459))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____8494)::rest_a,(p1,uu____8497)::rest_p) ->
                      let uu____8525 = matches_pat t1 p1 in
                      (match uu____8525 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____8539 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____8610 = matches_pat scrutinee1 p1 in
                      (match uu____8610 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____8620  ->
                                 let uu____8621 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____8622 =
                                   let uu____8623 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____8623
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____8621 uu____8622);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____8632 =
                                        let uu____8633 =
                                          let uu____8643 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____8643, false) in
                                        Clos uu____8633 in
                                      uu____8632 :: env2) env1 s in
                             let uu____8666 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____8666))) in
                let uu____8667 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____8667
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___147_8681  ->
                match uu___147_8681 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____8684 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____8688 -> d in
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
            let uu___202_8708 = config s e in
            {
              steps = (uu___202_8708.steps);
              tcenv = (uu___202_8708.tcenv);
              delta_level = (uu___202_8708.delta_level);
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
      fun t  -> let uu____8727 = config s e in norm_comp uu____8727 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____8734 = config [] env in norm_universe uu____8734 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____8741 = config [] env in ghost_to_pure_aux uu____8741 [] c
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
        let uu____8753 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____8753 in
      let uu____8754 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____8754
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___203_8756 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___203_8756.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___203_8756.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____8757  ->
                    let uu____8758 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____8758))
            }
        | None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____8766 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____8766
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____8773 =
        let uu____8774 = config [AllowUnboundUniverses] env in
        norm_comp uu____8774 [] c in
      FStar_Syntax_Print.comp_to_string uu____8773
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
                   let uu____8811 =
                     let uu____8812 =
                       let uu____8817 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____8817) in
                     FStar_Syntax_Syntax.Tm_refine uu____8812 in
                   mk uu____8811 t01.FStar_Syntax_Syntax.pos
               | uu____8822 -> t2)
          | uu____8823 -> t2 in
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
        let uu____8839 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____8839 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____8855 ->
                 let uu____8859 = FStar_Syntax_Util.abs_formals e in
                 (match uu____8859 with
                  | (actuals,uu____8870,uu____8871) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____8893 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____8893 with
                         | (binders,args) ->
                             let uu____8903 =
                               (FStar_Syntax_Syntax.mk_Tm_app e args) None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____8908 =
                               let uu____8915 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_33  -> FStar_Util.Inl _0_33) in
                               FStar_All.pipe_right uu____8915
                                 (fun _0_34  -> Some _0_34) in
                             FStar_Syntax_Util.abs binders uu____8903
                               uu____8908)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____8951 =
        let uu____8955 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8955, (t.FStar_Syntax_Syntax.n)) in
      match uu____8951 with
      | (Some sort,uu____8962) ->
          let uu____8964 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____8964
      | (uu____8965,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____8969 ->
          let uu____8973 = FStar_Syntax_Util.head_and_args t in
          (match uu____8973 with
           | (head1,args) ->
               let uu____8999 =
                 let uu____9000 = FStar_Syntax_Subst.compress head1 in
                 uu____9000.FStar_Syntax_Syntax.n in
               (match uu____8999 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____9003,thead) ->
                    let uu____9017 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____9017 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____9048 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_9052 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_9052.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_9052.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_9052.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_9052.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_9052.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_9052.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_9052.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_9052.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_9052.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_9052.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_9052.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_9052.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_9052.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_9052.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_9052.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_9052.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_9052.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_9052.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_9052.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_9052.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_9052.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_9052.FStar_TypeChecker_Env.proof_ns)
                                 }) t in
                            match uu____9048 with
                            | (uu____9053,ty,uu____9055) ->
                                eta_expand_with_type env t ty))
                | uu____9056 ->
                    let uu____9057 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_9061 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_9061.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_9061.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_9061.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_9061.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_9061.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_9061.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_9061.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_9061.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_9061.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_9061.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_9061.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_9061.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_9061.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_9061.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_9061.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_9061.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_9061.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_9061.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_9061.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_9061.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_9061.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_9061.FStar_TypeChecker_Env.proof_ns)
                         }) t in
                    (match uu____9057 with
                     | (uu____9062,ty,uu____9064) ->
                         eta_expand_with_type env t ty)))