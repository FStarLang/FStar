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
  | CheckNoUvars
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
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____68 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____72 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____76 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____80 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____84 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____88 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____92 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____96 -> false
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
  fun uu___131_233  ->
    match uu___131_233 with
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
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____667 = FStar_ST.read r in
  match uu____667 with
  | Some uu____672 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____681 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____681 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___132_686  ->
    match uu___132_686 with
    | Arg (c,uu____688,uu____689) ->
        let uu____690 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____690
    | MemoLazy uu____691 -> "MemoLazy"
    | Abs (uu____695,bs,uu____697,uu____698,uu____699) ->
        let uu____706 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____706
    | UnivArgs uu____711 -> "UnivArgs"
    | Match uu____715 -> "Match"
    | App (t,uu____720,uu____721) ->
        let uu____722 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____722
    | Meta (m,uu____724) -> "Meta"
    | Let uu____725 -> "Let"
    | Steps (uu____730,uu____731,uu____732) -> "Steps"
    | Debug t ->
        let uu____738 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____738
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____744 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____744 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____758 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____758 then f () else ()
let is_empty uu___133_767 =
  match uu___133_767 with | [] -> true | uu____769 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____791 ->
      let uu____792 =
        let uu____793 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____793 in
      failwith uu____792
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
          let uu____824 =
            FStar_List.fold_left
              (fun uu____842  ->
                 fun u1  ->
                   match uu____842 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____857 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____857 with
                        | (k_u,n1) ->
                            let uu____866 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____866
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____824 with
          | (uu____876,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____895 = FStar_List.nth env x in
                 match uu____895 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____898 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____905 ->
                   let uu____906 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____906
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____910 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              ->
              let uu____915 =
                let uu____916 = FStar_Syntax_Print.univ_to_string u2 in
                FStar_Util.format1
                  "CheckNoUvars: unexpected universes variable remains: %s"
                  uu____916 in
              failwith uu____915
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____918 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____923 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____928 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____928 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____939 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____939 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____944 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____951 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____951 with
                                  | (uu____954,m) -> n1 <= m)) in
                        if uu____944 then rest1 else us1
                    | uu____958 -> us1)
               | uu____961 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____964 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____964 in
        let uu____966 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____966
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____968 = aux u in
           match uu____968 with
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
          (fun uu____1068  ->
             let uu____1069 = FStar_Syntax_Print.tag_of_term t in
             let uu____1070 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1069
               uu____1070);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1071 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1074 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_constant uu____1099 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_name uu____1104 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_fvar uu____1109 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_uvar uu____1114 ->
                  let uu____1125 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1125
                  then
                    let uu____1126 =
                      let uu____1127 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1128 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1127 uu____1128 in
                    failwith uu____1126
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1131 =
                    let uu____1132 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1132 in
                  mk uu____1131 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1139 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1139
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1141 = lookup_bvar env x in
                  (match uu____1141 with
                   | Univ uu____1142 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1146) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1214 = closures_as_binders_delayed cfg env bs in
                  (match uu____1214 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1234 =
                         let uu____1235 =
                           let uu____1250 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1250) in
                         FStar_Syntax_Syntax.Tm_abs uu____1235 in
                       mk uu____1234 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1280 = closures_as_binders_delayed cfg env bs in
                  (match uu____1280 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1311 =
                    let uu____1318 =
                      let uu____1322 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1322] in
                    closures_as_binders_delayed cfg env uu____1318 in
                  (match uu____1311 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1336 =
                         let uu____1337 =
                           let uu____1342 =
                             let uu____1343 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1343
                               FStar_Pervasives.fst in
                           (uu____1342, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1337 in
                       mk uu____1336 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1411 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1411
                    | FStar_Util.Inr c ->
                        let uu____1425 = close_comp cfg env c in
                        FStar_Util.Inr uu____1425 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1440 =
                    let uu____1441 =
                      let uu____1459 = closure_as_term_delayed cfg env t11 in
                      (uu____1459, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1441 in
                  mk uu____1440 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1497 =
                    let uu____1498 =
                      let uu____1503 = closure_as_term_delayed cfg env t' in
                      let uu____1506 =
                        let uu____1507 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1507 in
                      (uu____1503, uu____1506) in
                    FStar_Syntax_Syntax.Tm_meta uu____1498 in
                  mk uu____1497 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1549 =
                    let uu____1550 =
                      let uu____1555 = closure_as_term_delayed cfg env t' in
                      let uu____1558 =
                        let uu____1559 =
                          let uu____1564 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1564) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1559 in
                      (uu____1555, uu____1558) in
                    FStar_Syntax_Syntax.Tm_meta uu____1550 in
                  mk uu____1549 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1583 =
                    let uu____1584 =
                      let uu____1589 = closure_as_term_delayed cfg env t' in
                      let uu____1592 =
                        let uu____1593 =
                          let uu____1599 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1599) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1593 in
                      (uu____1589, uu____1592) in
                    FStar_Syntax_Syntax.Tm_meta uu____1584 in
                  mk uu____1583 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1612 =
                    let uu____1613 =
                      let uu____1618 = closure_as_term_delayed cfg env t' in
                      (uu____1618, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1613 in
                  mk uu____1612 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1641  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____1647 =
                    let uu____1654 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____1654
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____1667 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___147_1671 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_1671.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_1671.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____1667)) in
                  (match uu____1647 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___148_1683 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___148_1683.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___148_1683.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____1690,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1716  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1721 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1721
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1727  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____1734 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1734
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___149_1742 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___149_1742.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___149_1742.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_31  -> FStar_Util.Inl _0_31)) in
                    let uu___150_1743 = lb in
                    let uu____1744 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1743.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1743.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1744
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1757  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1808 =
                    match uu____1808 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1846 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1859 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1897  ->
                                        fun uu____1898  ->
                                          match (uu____1897, uu____1898) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1952 =
                                                norm_pat env3 p1 in
                                              (match uu____1952 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1859 with
                               | (pats1,env3) ->
                                   ((let uu___151_2006 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___151_2006.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___152_2017 = x in
                                let uu____2018 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_2017.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_2017.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2018
                                } in
                              ((let uu___153_2024 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_2024.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___154_2028 = x in
                                let uu____2029 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___154_2028.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___154_2028.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2029
                                } in
                              ((let uu___155_2035 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___155_2035.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___156_2044 = x in
                                let uu____2045 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_2044.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_2044.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2045
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___157_2052 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_2052.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2054 = norm_pat env1 pat in
                        (match uu____2054 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2074 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2074 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2078 =
                    let uu____2079 =
                      let uu____2094 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2094) in
                    FStar_Syntax_Syntax.Tm_match uu____2079 in
                  mk uu____2078 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2141 -> closure_as_term cfg env t
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
        | uu____2157 ->
            FStar_List.map
              (fun uu____2171  ->
                 match uu____2171 with
                 | (x,imp) ->
                     let uu____2186 = closure_as_term_delayed cfg env x in
                     (uu____2186, imp)) args
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
        let uu____2198 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2230  ->
                  fun uu____2231  ->
                    match (uu____2230, uu____2231) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___158_2275 = b in
                          let uu____2276 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___158_2275.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___158_2275.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2276
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2198 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2323 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2335 = closure_as_term_delayed cfg env t in
                 let uu____2336 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2335 uu____2336
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2346 = closure_as_term_delayed cfg env t in
                 let uu____2347 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2346 uu____2347
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
                        (fun uu___134_2366  ->
                           match uu___134_2366 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2370 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2370
                           | f -> f)) in
                 let uu____2374 =
                   let uu___159_2375 = c1 in
                   let uu____2376 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2376;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___159_2375.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2374)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___135_2382  ->
            match uu___135_2382 with
            | FStar_Syntax_Syntax.DECREASES uu____2383 -> false
            | uu____2386 -> true))
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
            let uu____2414 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2414
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2431 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2431
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2457 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2481 =
      let uu____2482 =
        let uu____2488 = FStar_Util.string_of_int i in (uu____2488, None) in
      FStar_Const.Const_int uu____2482 in
    const_as_tm uu____2481 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2515 =
    match uu____2515 with
    | (a,uu____2520) ->
        let uu____2522 =
          let uu____2523 = FStar_Syntax_Subst.compress a in
          uu____2523.FStar_Syntax_Syntax.n in
        (match uu____2522 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2533 = FStar_Util.int_of_string i in Some uu____2533
         | uu____2534 -> None) in
  let arg_as_bounded_int uu____2543 =
    match uu____2543 with
    | (a,uu____2550) ->
        let uu____2554 =
          let uu____2555 = FStar_Syntax_Subst.compress a in
          uu____2555.FStar_Syntax_Syntax.n in
        (match uu____2554 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2562;
                FStar_Syntax_Syntax.pos = uu____2563;
                FStar_Syntax_Syntax.vars = uu____2564;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2566;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2567;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2568;_},uu____2569)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2596 =
               let uu____2599 = FStar_Util.int_of_string i in
               (fv1, uu____2599) in
             Some uu____2596
         | uu____2602 -> None) in
  let arg_as_bool uu____2611 =
    match uu____2611 with
    | (a,uu____2616) ->
        let uu____2618 =
          let uu____2619 = FStar_Syntax_Subst.compress a in
          uu____2619.FStar_Syntax_Syntax.n in
        (match uu____2618 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2624 -> None) in
  let arg_as_char uu____2631 =
    match uu____2631 with
    | (a,uu____2636) ->
        let uu____2638 =
          let uu____2639 = FStar_Syntax_Subst.compress a in
          uu____2639.FStar_Syntax_Syntax.n in
        (match uu____2638 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2644 -> None) in
  let arg_as_string uu____2651 =
    match uu____2651 with
    | (a,uu____2656) ->
        let uu____2658 =
          let uu____2659 = FStar_Syntax_Subst.compress a in
          uu____2659.FStar_Syntax_Syntax.n in
        (match uu____2658 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2664)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2667 -> None) in
  let arg_as_list f uu____2688 =
    match uu____2688 with
    | (a,uu____2697) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2714 -> None
          | (Some x)::xs ->
              let uu____2724 = sequence xs in
              (match uu____2724 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2735 = FStar_Syntax_Util.list_elements a in
        (match uu____2735 with
         | None  -> None
         | Some elts ->
             let uu____2745 =
               FStar_List.map
                 (fun x  ->
                    let uu____2752 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2752) elts in
             sequence uu____2745) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2782 = f a in Some uu____2782
    | uu____2783 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2822 = f a0 a1 in Some uu____2822
    | uu____2823 -> None in
  let unary_op as_a f r args =
    let uu____2867 = FStar_List.map as_a args in lift_unary (f r) uu____2867 in
  let binary_op as_a f r args =
    let uu____2917 = FStar_List.map as_a args in lift_binary (f r) uu____2917 in
  let as_primitive_step uu____2934 =
    match uu____2934 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2975 = f x in int_as_const r uu____2975) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3002 = f x y in int_as_const r uu____3002) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____3022 = f x in bool_as_const r uu____3022) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3049 = f x y in bool_as_const r uu____3049) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3076 = f x y in string_as_const r uu____3076) in
  let list_of_string' rng s =
    let name l =
      let uu____3090 =
        let uu____3091 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3091 in
      mk uu____3090 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3101 =
      let uu____3103 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3103 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3101 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3125 = FStar_Util.string_of_int i in
    string_as_const rng uu____3125 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3141 = FStar_Util.string_of_int i in
    string_as_const rng uu____3141 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3160 =
      let uu____3170 =
        let uu____3180 =
          let uu____3190 =
            let uu____3200 =
              let uu____3210 =
                let uu____3220 =
                  let uu____3230 =
                    let uu____3240 =
                      let uu____3250 =
                        let uu____3260 =
                          let uu____3270 =
                            let uu____3280 =
                              let uu____3290 =
                                let uu____3300 =
                                  let uu____3310 =
                                    let uu____3320 =
                                      let uu____3329 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3329, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3335 =
                                      let uu____3345 =
                                        let uu____3354 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3354, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3345] in
                                    uu____3320 :: uu____3335 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3310 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3300 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3290 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3280 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3270 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3260 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3250 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3240 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3230 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3220 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3210 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3200 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3190 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3180 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3170 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3160 in
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
      let uu____3697 =
        let uu____3698 =
          let uu____3699 = FStar_Syntax_Syntax.as_arg c in [uu____3699] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3698 in
      uu____3697 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3726 =
              let uu____3735 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3735, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3751  ->
                        fun uu____3752  ->
                          match (uu____3751, uu____3752) with
                          | ((int_to_t1,x),(uu____3763,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3769 =
              let uu____3779 =
                let uu____3788 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3788, (Prims.parse_int "2"),
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
                          fun uu____3857  ->
                            fun uu____3858  ->
                              match (uu____3857, uu____3858) with
                              | ((int_to_t1,x),(uu____3869,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3832] in
              uu____3779 :: uu____3822 in
            uu____3726 :: uu____3769)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3934)::(a1,uu____3936)::(a2,uu____3938)::[] ->
        let uu____3967 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3967 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3969 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3969
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3974 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3974
         | uu____3979 -> None)
    | uu____3980 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3992)::(a1,uu____3994)::(a2,uu____3996)::[] ->
        let uu____4025 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4025 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___160_4030 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_4030.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_4030.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_4030.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___161_4038 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4038.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4038.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4038.FStar_Syntax_Syntax.vars)
                })
         | uu____4043 -> None)
    | (_typ,uu____4045)::uu____4046::(a1,uu____4048)::(a2,uu____4050)::[] ->
        let uu____4087 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4087 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___160_4092 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_4092.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_4092.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_4092.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___161_4100 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4100.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4100.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4100.FStar_Syntax_Syntax.vars)
                })
         | uu____4105 -> None)
    | uu____4106 -> failwith "Unexpected number of arguments" in
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
      let uu____4117 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4117
      then tm
      else
        (let uu____4119 = FStar_Syntax_Util.head_and_args tm in
         match uu____4119 with
         | (head1,args) ->
             let uu____4145 =
               let uu____4146 = FStar_Syntax_Util.un_uinst head1 in
               uu____4146.FStar_Syntax_Syntax.n in
             (match uu____4145 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4150 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4150 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4163 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4163 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4166 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___162_4175 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___162_4175.tcenv);
           delta_level = (uu___162_4175.delta_level);
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
        let uu___163_4197 = t in
        {
          FStar_Syntax_Syntax.n = (uu___163_4197.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___163_4197.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___163_4197.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4216 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4243 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4243
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4246;
                     FStar_Syntax_Syntax.pos = uu____4247;
                     FStar_Syntax_Syntax.vars = uu____4248;_},uu____4249);
                FStar_Syntax_Syntax.tk = uu____4250;
                FStar_Syntax_Syntax.pos = uu____4251;
                FStar_Syntax_Syntax.vars = uu____4252;_},args)
             ->
             let uu____4272 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4272
             then
               let uu____4273 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4273 with
                | (Some (true ),uu____4306)::(uu____4307,(arg,uu____4309))::[]
                    -> arg
                | (uu____4350,(arg,uu____4352))::(Some (true ),uu____4353)::[]
                    -> arg
                | (Some (false ),uu____4394)::uu____4395::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4433::(Some (false ),uu____4434)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4472 -> tm)
             else
               (let uu____4482 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4482
                then
                  let uu____4483 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4483 with
                  | (Some (true ),uu____4516)::uu____4517::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4555::(Some (true ),uu____4556)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4594)::(uu____4595,(arg,uu____4597))::[]
                      -> arg
                  | (uu____4638,(arg,uu____4640))::(Some (false ),uu____4641)::[]
                      -> arg
                  | uu____4682 -> tm
                else
                  (let uu____4692 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4692
                   then
                     let uu____4693 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4693 with
                     | uu____4726::(Some (true ),uu____4727)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4765)::uu____4766::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4804)::(uu____4805,(arg,uu____4807))::[]
                         -> arg
                     | uu____4848 -> tm
                   else
                     (let uu____4858 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4858
                      then
                        let uu____4859 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4859 with
                        | (Some (true ),uu____4892)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4916)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4940 -> tm
                      else
                        (let uu____4950 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4950
                         then
                           match args with
                           | (t,uu____4952)::[] ->
                               let uu____4965 =
                                 let uu____4966 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4966.FStar_Syntax_Syntax.n in
                               (match uu____4965 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4969::[],body,uu____4971) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4997 -> tm)
                                | uu____4999 -> tm)
                           | (uu____5000,Some (FStar_Syntax_Syntax.Implicit
                              uu____5001))::(t,uu____5003)::[] ->
                               let uu____5030 =
                                 let uu____5031 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5031.FStar_Syntax_Syntax.n in
                               (match uu____5030 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5034::[],body,uu____5036) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5062 -> tm)
                                | uu____5064 -> tm)
                           | uu____5065 -> tm
                         else
                           (let uu____5072 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5072
                            then
                              match args with
                              | (t,uu____5074)::[] ->
                                  let uu____5087 =
                                    let uu____5088 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5088.FStar_Syntax_Syntax.n in
                                  (match uu____5087 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5091::[],body,uu____5093) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5119 -> tm)
                                   | uu____5121 -> tm)
                              | (uu____5122,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5123))::
                                  (t,uu____5125)::[] ->
                                  let uu____5152 =
                                    let uu____5153 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5153.FStar_Syntax_Syntax.n in
                                  (match uu____5152 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5156::[],body,uu____5158) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5184 -> tm)
                                   | uu____5186 -> tm)
                              | uu____5187 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5195;
                FStar_Syntax_Syntax.pos = uu____5196;
                FStar_Syntax_Syntax.vars = uu____5197;_},args)
             ->
             let uu____5213 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5213
             then
               let uu____5214 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5214 with
                | (Some (true ),uu____5247)::(uu____5248,(arg,uu____5250))::[]
                    -> arg
                | (uu____5291,(arg,uu____5293))::(Some (true ),uu____5294)::[]
                    -> arg
                | (Some (false ),uu____5335)::uu____5336::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5374::(Some (false ),uu____5375)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5413 -> tm)
             else
               (let uu____5423 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5423
                then
                  let uu____5424 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5424 with
                  | (Some (true ),uu____5457)::uu____5458::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5496::(Some (true ),uu____5497)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5535)::(uu____5536,(arg,uu____5538))::[]
                      -> arg
                  | (uu____5579,(arg,uu____5581))::(Some (false ),uu____5582)::[]
                      -> arg
                  | uu____5623 -> tm
                else
                  (let uu____5633 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5633
                   then
                     let uu____5634 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5634 with
                     | uu____5667::(Some (true ),uu____5668)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5706)::uu____5707::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5745)::(uu____5746,(arg,uu____5748))::[]
                         -> arg
                     | uu____5789 -> tm
                   else
                     (let uu____5799 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5799
                      then
                        let uu____5800 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5800 with
                        | (Some (true ),uu____5833)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5857)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5881 -> tm
                      else
                        (let uu____5891 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5891
                         then
                           match args with
                           | (t,uu____5893)::[] ->
                               let uu____5906 =
                                 let uu____5907 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5907.FStar_Syntax_Syntax.n in
                               (match uu____5906 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5910::[],body,uu____5912) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5938 -> tm)
                                | uu____5940 -> tm)
                           | (uu____5941,Some (FStar_Syntax_Syntax.Implicit
                              uu____5942))::(t,uu____5944)::[] ->
                               let uu____5971 =
                                 let uu____5972 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5972.FStar_Syntax_Syntax.n in
                               (match uu____5971 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5975::[],body,uu____5977) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6003 -> tm)
                                | uu____6005 -> tm)
                           | uu____6006 -> tm
                         else
                           (let uu____6013 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6013
                            then
                              match args with
                              | (t,uu____6015)::[] ->
                                  let uu____6028 =
                                    let uu____6029 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6029.FStar_Syntax_Syntax.n in
                                  (match uu____6028 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6032::[],body,uu____6034) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6060 -> tm)
                                   | uu____6062 -> tm)
                              | (uu____6063,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6064))::
                                  (t,uu____6066)::[] ->
                                  let uu____6093 =
                                    let uu____6094 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6094.FStar_Syntax_Syntax.n in
                                  (match uu____6093 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6097::[],body,uu____6099) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6125 -> tm)
                                   | uu____6127 -> tm)
                              | uu____6128 -> tm
                            else reduce_equality cfg tm)))))
         | uu____6135 -> tm)
let is_norm_request hd1 args =
  let uu____6150 =
    let uu____6154 =
      let uu____6155 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6155.FStar_Syntax_Syntax.n in
    (uu____6154, args) in
  match uu____6150 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6160::uu____6161::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6164::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6166 -> false
let get_norm_request args =
  match args with
  | uu____6185::(tm,uu____6187)::[] -> tm
  | (tm,uu____6197)::[] -> tm
  | uu____6202 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___136_6209  ->
    match uu___136_6209 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6211;
           FStar_Syntax_Syntax.pos = uu____6212;
           FStar_Syntax_Syntax.vars = uu____6213;_},uu____6214,uu____6215))::uu____6216
        -> true
    | uu____6222 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6227 =
      let uu____6228 = FStar_Syntax_Util.un_uinst t in
      uu____6228.FStar_Syntax_Syntax.n in
    match uu____6227 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6232 -> false
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
            (fun uu____6350  ->
               let uu____6351 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6352 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6353 =
                 let uu____6354 =
                   let uu____6356 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6356 in
                 stack_to_string uu____6354 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6351
                 uu____6352 uu____6353);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6368 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_uvar uu____6389 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____6400 =
                 let uu____6401 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____6402 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____6401 uu____6402 in
               failwith uu____6400
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_uvar uu____6407 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____6422 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____6427 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6432;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6433;_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6439;
                 FStar_Syntax_Syntax.fv_delta = uu____6440;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6445;
                 FStar_Syntax_Syntax.fv_delta = uu____6446;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6447);_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6456;
                  FStar_Syntax_Syntax.pos = uu____6457;
                  FStar_Syntax_Syntax.vars = uu____6458;_},uu____6459)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let hd2 = closure_as_term cfg env hd1 in
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___164_6500 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___164_6500.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___164_6500.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___164_6500.FStar_Syntax_Syntax.vars)
                 } in
               (FStar_ST.write t2.FStar_Syntax_Syntax.tk None;
                (let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6533 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6533) && (is_norm_request hd1 args))
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
                 let uu___165_6546 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___165_6546.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___165_6546.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6551;
                  FStar_Syntax_Syntax.pos = uu____6552;
                  FStar_Syntax_Syntax.vars = uu____6553;_},a1::a2::rest)
               ->
               let uu____6587 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6587 with
                | (hd1,uu____6598) ->
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
                    (FStar_Const.Const_reflect uu____6653);
                  FStar_Syntax_Syntax.tk = uu____6654;
                  FStar_Syntax_Syntax.pos = uu____6655;
                  FStar_Syntax_Syntax.vars = uu____6656;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6679 = FStar_List.tl stack1 in
               norm cfg env uu____6679 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6682;
                  FStar_Syntax_Syntax.pos = uu____6683;
                  FStar_Syntax_Syntax.vars = uu____6684;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6707 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6707 with
                | (reify_head,uu____6718) ->
                    let a1 =
                      let uu____6734 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6734 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6737);
                            FStar_Syntax_Syntax.tk = uu____6738;
                            FStar_Syntax_Syntax.pos = uu____6739;
                            FStar_Syntax_Syntax.vars = uu____6740;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6765 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6773 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6773
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6780 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6780
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6783 =
                      let uu____6787 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6787, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6783 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___137_6797  ->
                         match uu___137_6797 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               if Prims.op_Negation should_delta
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6801 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6801 in
                  let uu____6802 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6802 with
                  | None  ->
                      (log cfg
                         (fun uu____6810  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6819  ->
                            let uu____6820 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6821 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6820 uu____6821);
                       (let t3 =
                          let uu____6823 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6823
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
                          | (UnivArgs (us',uu____6831))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6846 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6847 ->
                              let uu____6848 =
                                let uu____6849 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6849 in
                              failwith uu____6848
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6852 = lookup_bvar env x in
               (match uu____6852 with
                | Univ uu____6853 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6868 = FStar_ST.read r in
                      (match uu____6868 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6890  ->
                                 let uu____6891 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6892 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6891
                                   uu____6892);
                            (let uu____6893 =
                               let uu____6894 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6894.FStar_Syntax_Syntax.n in
                             match uu____6893 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6897 ->
                                 norm cfg env2 stack1 t'
                             | uu____6912 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6945)::uu____6946 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6951)::uu____6952 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6958,uu____6959))::stack_rest ->
                    (match c with
                     | Univ uu____6962 -> norm cfg (c :: env) stack_rest t1
                     | uu____6963 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6966::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6981  ->
                                         let uu____6982 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6982);
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
                                           (fun uu___138_6997  ->
                                              match uu___138_6997 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6998 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7002  ->
                                         let uu____7003 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7003);
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
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7025 ->
                                   let cfg1 =
                                     let uu___166_7033 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___166_7033.tcenv);
                                       delta_level =
                                         (uu___166_7033.delta_level);
                                       primitive_steps =
                                         (uu___166_7033.primitive_steps)
                                     } in
                                   let uu____7034 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7034)
                          | uu____7035::tl1 ->
                              (log cfg
                                 (fun uu____7047  ->
                                    let uu____7048 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7048);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___167_7074 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___167_7074.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7089  ->
                          let uu____7090 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7090);
                     norm cfg env stack2 t1)
                | (Debug uu____7091)::uu____7092 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7094 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7094
                    else
                      (let uu____7096 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7096 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7112  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7139 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7139 in
                                 let c1 =
                                   let uu____7141 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7141
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7151 -> lopt in
                           (log cfg
                              (fun uu____7161  ->
                                 let uu____7162 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7162);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7172 = cfg in
                               let uu____7173 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7172.steps);
                                 tcenv = (uu___168_7172.tcenv);
                                 delta_level = (uu___168_7172.delta_level);
                                 primitive_steps = uu____7173
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7184)::uu____7185 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7189 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7189
                    else
                      (let uu____7191 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7191 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7207  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7234 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7234 in
                                 let c1 =
                                   let uu____7236 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7236
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7246 -> lopt in
                           (log cfg
                              (fun uu____7256  ->
                                 let uu____7257 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7257);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7267 = cfg in
                               let uu____7268 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7267.steps);
                                 tcenv = (uu___168_7267.tcenv);
                                 delta_level = (uu___168_7267.delta_level);
                                 primitive_steps = uu____7268
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7279)::uu____7280 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7286 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7286
                    else
                      (let uu____7288 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7288 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7304  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7331 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7331 in
                                 let c1 =
                                   let uu____7333 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7333
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7343 -> lopt in
                           (log cfg
                              (fun uu____7353  ->
                                 let uu____7354 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7354);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7364 = cfg in
                               let uu____7365 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7364.steps);
                                 tcenv = (uu___168_7364.tcenv);
                                 delta_level = (uu___168_7364.delta_level);
                                 primitive_steps = uu____7365
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7376)::uu____7377 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7382 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7382
                    else
                      (let uu____7384 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7384 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7400  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7427 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7427 in
                                 let c1 =
                                   let uu____7429 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7429
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7439 -> lopt in
                           (log cfg
                              (fun uu____7449  ->
                                 let uu____7450 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7450);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7460 = cfg in
                               let uu____7461 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7460.steps);
                                 tcenv = (uu___168_7460.tcenv);
                                 delta_level = (uu___168_7460.delta_level);
                                 primitive_steps = uu____7461
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7472)::uu____7473 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7483 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7483
                    else
                      (let uu____7485 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7485 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7501  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7528 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7528 in
                                 let c1 =
                                   let uu____7530 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7530
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7540 -> lopt in
                           (log cfg
                              (fun uu____7550  ->
                                 let uu____7551 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7551);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7561 = cfg in
                               let uu____7562 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7561.steps);
                                 tcenv = (uu___168_7561.tcenv);
                                 delta_level = (uu___168_7561.delta_level);
                                 primitive_steps = uu____7562
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7573 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7573
                    else
                      (let uu____7575 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7575 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7591  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7618 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7618 in
                                 let c1 =
                                   let uu____7620 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7620
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7630 -> lopt in
                           (log cfg
                              (fun uu____7640  ->
                                 let uu____7641 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7641);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7651 = cfg in
                               let uu____7652 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7651.steps);
                                 tcenv = (uu___168_7651.tcenv);
                                 delta_level = (uu___168_7651.delta_level);
                                 primitive_steps = uu____7652
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
                      (fun uu____7690  ->
                         fun stack2  ->
                           match uu____7690 with
                           | (a,aq) ->
                               let uu____7698 =
                                 let uu____7699 =
                                   let uu____7703 =
                                     let uu____7704 =
                                       let uu____7714 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7714, false) in
                                     Clos uu____7704 in
                                   (uu____7703, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7699 in
                               uu____7698 :: stack2) args) in
               (log cfg
                  (fun uu____7738  ->
                     let uu____7739 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7739);
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
                             ((let uu___169_7761 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___169_7761.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___169_7761.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7762 ->
                      let uu____7765 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7765)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7768 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7768 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7784 =
                          let uu____7785 =
                            let uu____7790 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___170_7792 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_7792.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___170_7792.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7790) in
                          FStar_Syntax_Syntax.Tm_refine uu____7785 in
                        mk uu____7784 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7805 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7805
               else
                 (let uu____7807 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7807 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7813 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7821  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7813 c1 in
                      let t2 =
                        let uu____7828 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7828 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7871)::uu____7872 -> norm cfg env stack1 t11
                | (Arg uu____7877)::uu____7878 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7883;
                       FStar_Syntax_Syntax.pos = uu____7884;
                       FStar_Syntax_Syntax.vars = uu____7885;_},uu____7886,uu____7887))::uu____7888
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7894)::uu____7895 ->
                    norm cfg env stack1 t11
                | uu____7900 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7904  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7917 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7917
                        | FStar_Util.Inr c ->
                            let uu____7925 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7925 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7930 =
                        let uu____7931 =
                          let uu____7932 =
                            let uu____7950 = FStar_Syntax_Util.unascribe t12 in
                            (uu____7950, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____7932 in
                        mk uu____7931 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7930)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7998,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7999;
                              FStar_Syntax_Syntax.lbunivs = uu____8000;
                              FStar_Syntax_Syntax.lbtyp = uu____8001;
                              FStar_Syntax_Syntax.lbeff = uu____8002;
                              FStar_Syntax_Syntax.lbdef = uu____8003;_}::uu____8004),uu____8005)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8031 =
                 (let uu____8034 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8034) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8036 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8036))) in
               if uu____8031
               then
                 let env1 =
                   let uu____8039 =
                     let uu____8040 =
                       let uu____8050 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8050,
                         false) in
                     Clos uu____8040 in
                   uu____8039 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8074 =
                    let uu____8077 =
                      let uu____8078 =
                        let uu____8079 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8079
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8078] in
                    FStar_Syntax_Subst.open_term uu____8077 body in
                  match uu____8074 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____8089 = FStar_List.hd bs in fst uu____8089 in
                        FStar_Util.Inl
                          (let uu___171_8095 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___171_8095.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___171_8095.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___172_8097 = lb in
                        let uu____8098 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8097.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8097.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8098
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8110  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____8125 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____8125 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____8152 =
                               let uu___173_8153 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___173_8153.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___173_8153.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____8152 in
                           let uu____8154 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____8154 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____8182 =
                                   FStar_List.map (fun uu____8185  -> Dummy)
                                     lbs1 in
                                 let uu____8186 =
                                   let uu____8188 =
                                     FStar_List.map
                                       (fun uu____8193  -> Dummy) xs1 in
                                   FStar_List.append uu____8188 env in
                                 FStar_List.append uu____8182 uu____8186 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 None in
                               let uu___174_8203 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___174_8203.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___174_8203.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____8206 =
                        FStar_List.map (fun uu____8209  -> Dummy) lbs2 in
                      FStar_List.append uu____8206 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____8211 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____8211 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___175_8222 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.tk =
                               (uu___175_8222.FStar_Syntax_Syntax.tk);
                             FStar_Syntax_Syntax.pos =
                               (uu___175_8222.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___175_8222.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8243 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8243
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8256 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8287  ->
                        match uu____8287 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8326 =
                                let uu___176_8327 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___176_8327.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___176_8327.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8326 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8256 with
                | (rec_env,memos,uu____8387) ->
                    let uu____8402 =
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
                             let uu____8449 =
                               let uu____8450 =
                                 let uu____8460 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8460, false) in
                               Clos uu____8450 in
                             uu____8449 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8498;
                             FStar_Syntax_Syntax.pos = uu____8499;
                             FStar_Syntax_Syntax.vars = uu____8500;_},uu____8501,uu____8502))::uu____8503
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8509 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8516 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8516
                        then
                          let uu___177_8517 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___177_8517.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___177_8517.primitive_steps)
                          }
                        else
                          (let uu___178_8519 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___178_8519.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___178_8519.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8521 =
                         let uu____8522 = FStar_Syntax_Subst.compress head1 in
                         uu____8522.FStar_Syntax_Syntax.n in
                       match uu____8521 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8536 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8536 with
                            | (uu____8537,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8541 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8548 =
                                         let uu____8549 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8549.FStar_Syntax_Syntax.n in
                                       match uu____8548 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8554,uu____8555))
                                           ->
                                           let uu____8564 =
                                             let uu____8565 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8565.FStar_Syntax_Syntax.n in
                                           (match uu____8564 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8570,msrc,uu____8572))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8581 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8581
                                            | uu____8582 -> None)
                                       | uu____8583 -> None in
                                     let uu____8584 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8584 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___179_8588 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___179_8588.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___179_8588.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___179_8588.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8589 =
                                            FStar_List.tl stack1 in
                                          let uu____8590 =
                                            let uu____8591 =
                                              let uu____8594 =
                                                let uu____8595 =
                                                  let uu____8603 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8603) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8595 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8594 in
                                            uu____8591 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8589 uu____8590
                                      | None  ->
                                          let uu____8620 =
                                            let uu____8621 = is_return body in
                                            match uu____8621 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8624;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8625;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8626;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8631 -> false in
                                          if uu____8620
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
                                               let uu____8651 =
                                                 let uu____8654 =
                                                   let uu____8655 =
                                                     let uu____8670 =
                                                       let uu____8672 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8672] in
                                                     (uu____8670, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8655 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8654 in
                                               uu____8651 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8705 =
                                                 let uu____8706 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8706.FStar_Syntax_Syntax.n in
                                               match uu____8705 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8712::uu____8713::[])
                                                   ->
                                                   let uu____8719 =
                                                     let uu____8722 =
                                                       let uu____8723 =
                                                         let uu____8728 =
                                                           let uu____8730 =
                                                             let uu____8731 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8731 in
                                                           let uu____8732 =
                                                             let uu____8734 =
                                                               let uu____8735
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8735 in
                                                             [uu____8734] in
                                                           uu____8730 ::
                                                             uu____8732 in
                                                         (bind1, uu____8728) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8723 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8722 in
                                                   uu____8719 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8747 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8753 =
                                                 let uu____8756 =
                                                   let uu____8757 =
                                                     let uu____8767 =
                                                       let uu____8769 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8770 =
                                                         let uu____8772 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8773 =
                                                           let uu____8775 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8776 =
                                                             let uu____8778 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8779 =
                                                               let uu____8781
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8782
                                                                 =
                                                                 let uu____8784
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8784] in
                                                               uu____8781 ::
                                                                 uu____8782 in
                                                             uu____8778 ::
                                                               uu____8779 in
                                                           uu____8775 ::
                                                             uu____8776 in
                                                         uu____8772 ::
                                                           uu____8773 in
                                                       uu____8769 ::
                                                         uu____8770 in
                                                     (bind_inst, uu____8767) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8757 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8756 in
                                               uu____8753 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8796 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8796 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8814 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8814 with
                            | (uu____8815,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8838 =
                                        let uu____8839 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8839.FStar_Syntax_Syntax.n in
                                      match uu____8838 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8845) -> t4
                                      | uu____8850 -> head2 in
                                    let uu____8851 =
                                      let uu____8852 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8852.FStar_Syntax_Syntax.n in
                                    match uu____8851 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8857 -> None in
                                  let uu____8858 = maybe_extract_fv head2 in
                                  match uu____8858 with
                                  | Some x when
                                      let uu____8864 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8864
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8868 =
                                          maybe_extract_fv head3 in
                                        match uu____8868 with
                                        | Some uu____8871 -> Some true
                                        | uu____8872 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8875 -> (head2, None) in
                                ((let is_arg_impure uu____8886 =
                                    match uu____8886 with
                                    | (e,q) ->
                                        let uu____8891 =
                                          let uu____8892 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8892.FStar_Syntax_Syntax.n in
                                        (match uu____8891 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8907 -> false) in
                                  let uu____8908 =
                                    let uu____8909 =
                                      let uu____8913 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8913 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8909 in
                                  if uu____8908
                                  then
                                    let uu____8916 =
                                      let uu____8917 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8917 in
                                    failwith uu____8916
                                  else ());
                                 (let uu____8919 =
                                    maybe_unfold_action head_app in
                                  match uu____8919 with
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
                                      let uu____8954 = FStar_List.tl stack1 in
                                      norm cfg env uu____8954 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8968 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8968 in
                           let uu____8969 = FStar_List.tl stack1 in
                           norm cfg env uu____8969 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____9050  ->
                                     match uu____9050 with
                                     | (pat,wopt,tm) ->
                                         let uu____9084 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9084))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9108 = FStar_List.tl stack1 in
                           norm cfg env uu____9108 tm
                       | uu____9109 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9118;
                             FStar_Syntax_Syntax.pos = uu____9119;
                             FStar_Syntax_Syntax.vars = uu____9120;_},uu____9121,uu____9122))::uu____9123
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9129 -> false in
                    if should_reify
                    then
                      let uu____9130 = FStar_List.tl stack1 in
                      let uu____9131 =
                        let uu____9132 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9132 in
                      norm cfg env uu____9130 uu____9131
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9135 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9135
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___180_9141 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___180_9141.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___180_9141.primitive_steps)
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
                | uu____9143 ->
                    (match stack1 with
                     | uu____9144::uu____9145 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9149)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____9164 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9174 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9174
                           | uu____9181 -> m in
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
              let uu____9193 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9193 with
              | (uu____9194,return_repr) ->
                  let return_inst =
                    let uu____9201 =
                      let uu____9202 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9202.FStar_Syntax_Syntax.n in
                    match uu____9201 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9208::[])
                        ->
                        let uu____9214 =
                          let uu____9217 =
                            let uu____9218 =
                              let uu____9223 =
                                let uu____9225 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9225] in
                              (return_tm, uu____9223) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9218 in
                          FStar_Syntax_Syntax.mk uu____9217 in
                        uu____9214 None e.FStar_Syntax_Syntax.pos
                    | uu____9237 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9240 =
                    let uu____9243 =
                      let uu____9244 =
                        let uu____9254 =
                          let uu____9256 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9257 =
                            let uu____9259 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9259] in
                          uu____9256 :: uu____9257 in
                        (return_inst, uu____9254) in
                      FStar_Syntax_Syntax.Tm_app uu____9244 in
                    FStar_Syntax_Syntax.mk uu____9243 in
                  uu____9240 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9272 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9272 with
               | None  ->
                   let uu____9274 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9274
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9275;
                     FStar_TypeChecker_Env.mtarget = uu____9276;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9277;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9288;
                     FStar_TypeChecker_Env.mtarget = uu____9289;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9290;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9308 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9308)
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
                (fun uu____9342  ->
                   match uu____9342 with
                   | (a,imp) ->
                       let uu____9349 = norm cfg env [] a in
                       (uu____9349, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___181_9364 = comp1 in
            let uu____9367 =
              let uu____9368 =
                let uu____9374 = norm cfg env [] t in
                let uu____9375 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9374, uu____9375) in
              FStar_Syntax_Syntax.Total uu____9368 in
            {
              FStar_Syntax_Syntax.n = uu____9367;
              FStar_Syntax_Syntax.tk = (uu___181_9364.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___181_9364.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___181_9364.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___182_9390 = comp1 in
            let uu____9393 =
              let uu____9394 =
                let uu____9400 = norm cfg env [] t in
                let uu____9401 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9400, uu____9401) in
              FStar_Syntax_Syntax.GTotal uu____9394 in
            {
              FStar_Syntax_Syntax.n = uu____9393;
              FStar_Syntax_Syntax.tk = (uu___182_9390.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___182_9390.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___182_9390.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9436  ->
                      match uu____9436 with
                      | (a,i) ->
                          let uu____9443 = norm cfg env [] a in
                          (uu____9443, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___139_9451  ->
                      match uu___139_9451 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9455 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9455
                      | f -> f)) in
            let uu___183_9459 = comp1 in
            let uu____9462 =
              let uu____9463 =
                let uu___184_9464 = ct in
                let uu____9465 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9466 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9469 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9465;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___184_9464.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9466;
                  FStar_Syntax_Syntax.effect_args = uu____9469;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9463 in
            {
              FStar_Syntax_Syntax.n = uu____9462;
              FStar_Syntax_Syntax.tk = (uu___183_9459.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9459.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9459.FStar_Syntax_Syntax.vars)
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
            (let uu___185_9488 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___185_9488.tcenv);
               delta_level = (uu___185_9488.delta_level);
               primitive_steps = (uu___185_9488.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9493 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9493 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9496 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___186_9510 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___186_9510.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___186_9510.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_9510.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9520 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9520
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___187_9525 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___187_9525.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___187_9525.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___187_9525.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___187_9525.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___188_9527 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___188_9527.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___188_9527.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___188_9527.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___188_9527.FStar_Syntax_Syntax.flags)
                    } in
              let uu___189_9528 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___189_9528.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___189_9528.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___189_9528.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9534 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9537  ->
        match uu____9537 with
        | (x,imp) ->
            let uu____9540 =
              let uu___190_9541 = x in
              let uu____9542 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___190_9541.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___190_9541.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9542
              } in
            (uu____9540, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9548 =
          FStar_List.fold_left
            (fun uu____9560  ->
               fun b  ->
                 match uu____9560 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9548 with | (nbs,uu____9577) -> FStar_List.rev nbs
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
            let uu____9594 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9594
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9599 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9599
               then
                 let uu____9603 =
                   let uu____9606 =
                     let uu____9607 =
                       let uu____9610 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9610 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9607 in
                   FStar_Util.Inl uu____9606 in
                 Some uu____9603
               else
                 (let uu____9614 =
                    let uu____9617 =
                      let uu____9618 =
                        let uu____9621 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9621 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9618 in
                    FStar_Util.Inl uu____9617 in
                  Some uu____9614))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9634 -> lopt
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
              ((let uu____9646 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9646
                then
                  let uu____9647 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9648 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9647
                    uu____9648
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___191_9661 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___191_9661.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9683  ->
                    let uu____9684 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9684);
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
              let uu____9721 =
                let uu___192_9722 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___192_9722.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___192_9722.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___192_9722.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9721
          | (Arg (Univ uu____9727,uu____9728,uu____9729))::uu____9730 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9732,uu____9733))::uu____9734 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9746),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9764  ->
                    let uu____9765 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9765);
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
                 (let uu____9776 = FStar_ST.read m in
                  match uu____9776 with
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
                  | Some (uu____9802,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9824 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9824
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9833  ->
                    let uu____9834 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9834);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9839 =
                  log cfg
                    (fun uu____9844  ->
                       let uu____9845 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9846 =
                         let uu____9847 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9858  ->
                                   match uu____9858 with
                                   | (p,uu____9864,uu____9865) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9847
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9845 uu____9846);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___140_9876  ->
                               match uu___140_9876 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9877 -> false)) in
                     let steps' =
                       let uu____9880 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9880
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___193_9883 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___193_9883.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___193_9883.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9913 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9926 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9964  ->
                                   fun uu____9965  ->
                                     match (uu____9964, uu____9965) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____10019 = norm_pat env3 p1 in
                                         (match uu____10019 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9926 with
                          | (pats1,env3) ->
                              ((let uu___194_10073 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___194_10073.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___195_10084 = x in
                           let uu____10085 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___195_10084.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___195_10084.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10085
                           } in
                         ((let uu___196_10091 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___196_10091.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___197_10095 = x in
                           let uu____10096 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___197_10095.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___197_10095.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10096
                           } in
                         ((let uu___198_10102 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___198_10102.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___199_10111 = x in
                           let uu____10112 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___199_10111.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___199_10111.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10112
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___200_10119 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___200_10119.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10122 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10135 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10135 with
                                 | (p,wopt,e) ->
                                     let uu____10151 = norm_pat env1 p in
                                     (match uu____10151 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10172 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10172 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10176 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10176) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10186) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10191 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10192;
                        FStar_Syntax_Syntax.fv_delta = uu____10193;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10194;
                        FStar_Syntax_Syntax.fv_delta = uu____10195;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10196);_}
                      -> true
                  | uu____10200 -> false in
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
                  let uu____10296 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10296 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10328 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10330 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10332 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10344 ->
                                let uu____10345 =
                                  let uu____10346 = is_cons head1 in
                                  Prims.op_Negation uu____10346 in
                                FStar_Util.Inr uu____10345)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10358 =
                             let uu____10359 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10359.FStar_Syntax_Syntax.n in
                           (match uu____10358 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10366 ->
                                let uu____10367 =
                                  let uu____10368 = is_cons head1 in
                                  Prims.op_Negation uu____10368 in
                                FStar_Util.Inr uu____10367))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10399)::rest_a,(p1,uu____10402)::rest_p) ->
                      let uu____10430 = matches_pat t1 p1 in
                      (match uu____10430 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10444 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10515 = matches_pat scrutinee1 p1 in
                      (match uu____10515 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10528  ->
                                 let uu____10529 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10530 =
                                   let uu____10531 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10531
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10529 uu____10530);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10543 =
                                        let uu____10544 =
                                          let uu____10554 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10554, false) in
                                        Clos uu____10544 in
                                      uu____10543 :: env2) env1 s in
                             let uu____10577 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10577))) in
                let uu____10578 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10578
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___141_10594  ->
                match uu___141_10594 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____10597 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10601 -> d in
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
            let uu___201_10621 = config s e in
            {
              steps = (uu___201_10621.steps);
              tcenv = (uu___201_10621.tcenv);
              delta_level = (uu___201_10621.delta_level);
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
      fun t  -> let uu____10640 = config s e in norm_comp uu____10640 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10647 = config [] env in norm_universe uu____10647 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10654 = config [] env in ghost_to_pure_aux uu____10654 [] c
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
        let uu____10666 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10666 in
      let uu____10667 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10667
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___202_10669 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___202_10669.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___202_10669.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10672  ->
                    let uu____10673 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10673))
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
            ((let uu____10690 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10690);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10701 = config [AllowUnboundUniverses] env in
          norm_comp uu____10701 [] c
        with
        | e ->
            ((let uu____10708 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10708);
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
                   let uu____10745 =
                     let uu____10746 =
                       let uu____10751 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10751) in
                     FStar_Syntax_Syntax.Tm_refine uu____10746 in
                   mk uu____10745 t01.FStar_Syntax_Syntax.pos
               | uu____10756 -> t2)
          | uu____10757 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
let reduce_or_remove_uvar_solutions:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____10796 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10796 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10812 ->
                 let uu____10816 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10816 with
                  | (actuals,uu____10827,uu____10828) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10850 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10850 with
                         | (binders,args) ->
                             let uu____10860 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10863 =
                               let uu____10870 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_32  -> FStar_Util.Inl _0_32) in
                               FStar_All.pipe_right uu____10870
                                 (fun _0_33  -> Some _0_33) in
                             FStar_Syntax_Util.abs binders uu____10860
                               uu____10863)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10906 =
        let uu____10910 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10910, (t.FStar_Syntax_Syntax.n)) in
      match uu____10906 with
      | (Some sort,uu____10917) ->
          let uu____10919 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10919
      | (uu____10920,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10924 ->
          let uu____10928 = FStar_Syntax_Util.head_and_args t in
          (match uu____10928 with
           | (head1,args) ->
               let uu____10954 =
                 let uu____10955 = FStar_Syntax_Subst.compress head1 in
                 uu____10955.FStar_Syntax_Syntax.n in
               (match uu____10954 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10958,thead) ->
                    let uu____10976 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10976 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____11007 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___207_11012 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___207_11012.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___207_11012.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___207_11012.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___207_11012.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___207_11012.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___207_11012.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___207_11012.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___207_11012.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___207_11012.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___207_11012.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___207_11012.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___207_11012.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___207_11012.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___207_11012.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___207_11012.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___207_11012.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___207_11012.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___207_11012.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___207_11012.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___207_11012.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___207_11012.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____11007 with
                            | (uu____11013,ty,uu____11015) ->
                                eta_expand_with_type env t ty))
                | uu____11016 ->
                    let uu____11017 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___208_11022 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___208_11022.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___208_11022.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___208_11022.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___208_11022.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___208_11022.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___208_11022.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___208_11022.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___208_11022.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___208_11022.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___208_11022.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___208_11022.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___208_11022.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___208_11022.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___208_11022.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___208_11022.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___208_11022.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___208_11022.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___208_11022.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___208_11022.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___208_11022.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___208_11022.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____11017 with
                     | (uu____11023,ty,uu____11025) ->
                         eta_expand_with_type env t ty)))
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list*
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.comp',Prims.unit)
                                        FStar_Syntax_Syntax.syntax)
            FStar_Util.either)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____11071,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c)) None
                  c.FStar_Syntax_Syntax.pos
            | (uu____11079,FStar_Util.Inl t) ->
                let uu____11083 =
                  let uu____11086 =
                    let uu____11087 =
                      let uu____11095 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____11095) in
                    FStar_Syntax_Syntax.Tm_arrow uu____11087 in
                  FStar_Syntax_Syntax.mk uu____11086 in
                uu____11083 None t.FStar_Syntax_Syntax.pos in
          let uu____11104 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____11104 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____11121 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____11153 ->
                    let uu____11154 =
                      let uu____11159 =
                        let uu____11160 = FStar_Syntax_Subst.compress t3 in
                        uu____11160.FStar_Syntax_Syntax.n in
                      (uu____11159, tc) in
                    (match uu____11154 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____11176) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____11200) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____11226,FStar_Util.Inl uu____11227) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____11241 -> failwith "Impossible") in
              (match uu____11121 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____11306 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____11306 with
          | (univ_names1,binders1,tc) ->
              let uu____11340 = FStar_Util.left tc in
              (univ_names1, binders1, uu____11340)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list*
            (FStar_Syntax_Syntax.comp',Prims.unit)
            FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____11366 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____11366 with
          | (univ_names1,binders1,tc) ->
              let uu____11402 = FStar_Util.right tc in
              (univ_names1, binders1, uu____11402)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____11428 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____11428 with
           | (univ_names1,binders1,typ1) ->
               let uu___209_11444 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_11444.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_11444.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_11444.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___210_11456 = s in
          let uu____11457 =
            let uu____11458 =
              let uu____11463 = FStar_List.map (elim_uvars env) sigs in
              (uu____11463, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____11458 in
          {
            FStar_Syntax_Syntax.sigel = uu____11457;
            FStar_Syntax_Syntax.sigrng =
              (uu___210_11456.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_11456.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_11456.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____11475 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11475 with
           | (univ_names1,uu____11485,typ1) ->
               let uu___211_11493 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_11493.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_11493.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_11493.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____11498 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11498 with
           | (univ_names1,uu____11508,typ1) ->
               let uu___212_11516 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___212_11516.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___212_11516.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___212_11516.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids,attrs) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____11543 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____11543 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____11558 =
                            let uu____11559 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____11559 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____11558 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___213_11562 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___213_11562.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___213_11562.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___214_11563 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids, attrs));
            FStar_Syntax_Syntax.sigrng =
              (uu___214_11563.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_11563.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_11563.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___215_11571 = s in
          let uu____11572 =
            let uu____11573 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____11573 in
          {
            FStar_Syntax_Syntax.sigel = uu____11572;
            FStar_Syntax_Syntax.sigrng =
              (uu___215_11571.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___215_11571.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___215_11571.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____11577 = elim_uvars_aux_t env us [] t in
          (match uu____11577 with
           | (us1,uu____11587,t1) ->
               let uu___216_11595 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_11595.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_11595.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_11595.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11596 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11598 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____11598 with
           | (univs1,binders,signature) ->
               let uu____11614 =
                 let uu____11619 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____11619 with
                 | (univs_opening,univs2) ->
                     let uu____11634 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____11634) in
               (match uu____11614 with
                | (univs_opening,univs_closing) ->
                    let uu____11644 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____11648 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____11649 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____11648, uu____11649) in
                    (match uu____11644 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____11666 =
                           match uu____11666 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____11678 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____11678 with
                                | (us1,t1) ->
                                    let uu____11685 =
                                      let uu____11688 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____11692 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____11688, uu____11692) in
                                    (match uu____11685 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____11700 =
                                           let uu____11703 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____11708 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____11703, uu____11708) in
                                         (match uu____11700 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____11718 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____11718 in
                                              let uu____11719 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____11719 with
                                               | (uu____11730,uu____11731,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____11740 =
                                                       let uu____11741 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____11741 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____11740 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____11746 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____11746 with
                           | (uu____11753,uu____11754,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_ascribed
                                  ((a.FStar_Syntax_Syntax.action_defn),
                                    ((FStar_Util.Inl
                                        (a.FStar_Syntax_Syntax.action_typ)),
                                      None), None)) None
                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_typ_templ t =
                             let uu____11804 =
                               let uu____11805 =
                                 FStar_Syntax_Subst.compress t in
                               uu____11805.FStar_Syntax_Syntax.n in
                             match uu____11804 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl typ,None ),None ) ->
                                 (defn, typ)
                             | uu____11853 -> failwith "Impossible" in
                           let uu____11860 =
                             elim_uvars_aux_t env
                               (FStar_List.append univs1
                                  a.FStar_Syntax_Syntax.action_univs)
                               (FStar_List.append binders
                                  a.FStar_Syntax_Syntax.action_params)
                               action_typ_templ in
                           match uu____11860 with
                           | (u_action_univs,b_action_params,res) ->
                               let action_univs =
                                 FStar_Util.nth_tail n1 u_action_univs in
                               let action_params =
                                 FStar_Util.nth_tail
                                   (FStar_List.length binders)
                                   b_action_params in
                               let uu____11892 =
                                 destruct_action_typ_templ res in
                               (match uu____11892 with
                                | (action_defn,action_typ) ->
                                    let uu___217_11909 = a in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        (uu___217_11909.FStar_Syntax_Syntax.action_name);
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (uu___217_11909.FStar_Syntax_Syntax.action_unqualified_name);
                                      FStar_Syntax_Syntax.action_univs =
                                        action_univs;
                                      FStar_Syntax_Syntax.action_params =
                                        action_params;
                                      FStar_Syntax_Syntax.action_defn =
                                        action_defn;
                                      FStar_Syntax_Syntax.action_typ =
                                        action_typ
                                    }) in
                         let ed1 =
                           let uu___218_11911 = ed in
                           let uu____11912 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____11913 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____11914 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____11915 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____11916 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____11917 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____11918 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____11919 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____11920 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____11921 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____11922 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____11923 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____11924 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____11925 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___218_11911.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___218_11911.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____11912;
                             FStar_Syntax_Syntax.bind_wp = uu____11913;
                             FStar_Syntax_Syntax.if_then_else = uu____11914;
                             FStar_Syntax_Syntax.ite_wp = uu____11915;
                             FStar_Syntax_Syntax.stronger = uu____11916;
                             FStar_Syntax_Syntax.close_wp = uu____11917;
                             FStar_Syntax_Syntax.assert_p = uu____11918;
                             FStar_Syntax_Syntax.assume_p = uu____11919;
                             FStar_Syntax_Syntax.null_wp = uu____11920;
                             FStar_Syntax_Syntax.trivial = uu____11921;
                             FStar_Syntax_Syntax.repr = uu____11922;
                             FStar_Syntax_Syntax.return_repr = uu____11923;
                             FStar_Syntax_Syntax.bind_repr = uu____11924;
                             FStar_Syntax_Syntax.actions = uu____11925
                           } in
                         let uu___219_11927 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___219_11927.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___219_11927.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___219_11927.FStar_Syntax_Syntax.sigmeta)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___142_11938 =
            match uu___142_11938 with
            | None  -> None
            | Some (us,t) ->
                let uu____11953 = elim_uvars_aux_t env us [] t in
                (match uu____11953 with
                 | (us1,uu____11966,t1) -> Some (us1, t1)) in
          let sub_eff1 =
            let uu___220_11977 = sub_eff in
            let uu____11978 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____11980 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___220_11977.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___220_11977.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____11978;
              FStar_Syntax_Syntax.lift = uu____11980
            } in
          let uu___221_11982 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___221_11982.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___221_11982.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___221_11982.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____11990 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____11990 with
           | (univ_names1,binders1,comp1) ->
               let uu___222_12012 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_12012.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_12012.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_12012.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____12019 -> s