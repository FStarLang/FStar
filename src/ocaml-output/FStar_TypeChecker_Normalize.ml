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
  | uu____787 ->
      let uu____788 =
        let uu____789 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____789 in
      failwith uu____788
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
          let uu____820 =
            FStar_List.fold_left
              (fun uu____829  ->
                 fun u1  ->
                   match uu____829 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____844 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____844 with
                        | (k_u,n1) ->
                            let uu____853 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____853
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____820 with
          | (uu____863,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____879 = FStar_List.nth env x in
                 match uu____879 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____882 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____886 ->
                   let uu____887 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____887
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____891 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              ->
              let uu____896 =
                let uu____897 = FStar_Syntax_Print.univ_to_string u2 in
                FStar_Util.format1
                  "CheckNoUvars: unexpected universes variable remains: %s"
                  uu____897 in
              failwith uu____896
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____899 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____904 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____909 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____909 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____920 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____920 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____925 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____928 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____928 with
                                  | (uu____931,m) -> n1 <= m)) in
                        if uu____925 then rest1 else us1
                    | uu____935 -> us1)
               | uu____938 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____941 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____941 in
        let uu____943 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____943
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____945 = aux u in
           match uu____945 with
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
          (fun uu____1042  ->
             let uu____1043 = FStar_Syntax_Print.tag_of_term t in
             let uu____1044 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1043
               uu____1044);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1045 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1048 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_constant uu____1073 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_name uu____1078 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_fvar uu____1083 ->
                  (FStar_ST.write t1.FStar_Syntax_Syntax.tk None; t1)
              | FStar_Syntax_Syntax.Tm_uvar uu____1088 ->
                  let uu____1099 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1099
                  then
                    let uu____1100 =
                      let uu____1101 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format1
                        "CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1101 in
                    failwith uu____1100
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1104 =
                    let uu____1105 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1105 in
                  mk uu____1104 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1112 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1112
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1114 = lookup_bvar env x in
                  (match uu____1114 with
                   | Univ uu____1115 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1119) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1187 = closures_as_binders_delayed cfg env bs in
                  (match uu____1187 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1207 =
                         let uu____1208 =
                           let uu____1223 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1223) in
                         FStar_Syntax_Syntax.Tm_abs uu____1208 in
                       mk uu____1207 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1253 = closures_as_binders_delayed cfg env bs in
                  (match uu____1253 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1284 =
                    let uu____1291 =
                      let uu____1295 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1295] in
                    closures_as_binders_delayed cfg env uu____1291 in
                  (match uu____1284 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1309 =
                         let uu____1310 =
                           let uu____1315 =
                             let uu____1316 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1316
                               FStar_Pervasives.fst in
                           (uu____1315, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1310 in
                       mk uu____1309 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1384 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1384
                    | FStar_Util.Inr c ->
                        let uu____1398 = close_comp cfg env c in
                        FStar_Util.Inr uu____1398 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1413 =
                    let uu____1414 =
                      let uu____1432 = closure_as_term_delayed cfg env t11 in
                      (uu____1432, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1414 in
                  mk uu____1413 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1470 =
                    let uu____1471 =
                      let uu____1476 = closure_as_term_delayed cfg env t' in
                      let uu____1479 =
                        let uu____1480 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1480 in
                      (uu____1476, uu____1479) in
                    FStar_Syntax_Syntax.Tm_meta uu____1471 in
                  mk uu____1470 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1522 =
                    let uu____1523 =
                      let uu____1528 = closure_as_term_delayed cfg env t' in
                      let uu____1531 =
                        let uu____1532 =
                          let uu____1537 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1537) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1532 in
                      (uu____1528, uu____1531) in
                    FStar_Syntax_Syntax.Tm_meta uu____1523 in
                  mk uu____1522 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1556 =
                    let uu____1557 =
                      let uu____1562 = closure_as_term_delayed cfg env t' in
                      let uu____1565 =
                        let uu____1566 =
                          let uu____1572 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1572) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1566 in
                      (uu____1562, uu____1565) in
                    FStar_Syntax_Syntax.Tm_meta uu____1557 in
                  mk uu____1556 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1585 =
                    let uu____1586 =
                      let uu____1591 = closure_as_term_delayed cfg env t' in
                      (uu____1591, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1586 in
                  mk uu____1585 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1612  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____1618 =
                    let uu____1625 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____1625
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____1638 =
                         closure_as_term cfg (Dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___147_1641 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_1641.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_1641.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____1638)) in
                  (match uu____1618 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___148_1653 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___148_1653.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___148_1653.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____1660,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1684  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1689 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1689
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1693  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____1700 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1700
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___149_1707 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___149_1707.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___149_1707.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_31  -> FStar_Util.Inl _0_31)) in
                    let uu___150_1708 = lb in
                    let uu____1709 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1708.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1708.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1709
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1720  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1771 =
                    match uu____1771 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1809 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1822 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1851  ->
                                        fun uu____1852  ->
                                          match (uu____1851, uu____1852) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1906 =
                                                norm_pat env3 p1 in
                                              (match uu____1906 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1822 with
                               | (pats1,env3) ->
                                   ((let uu___151_1959 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___151_1959.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___152_1970 = x in
                                let uu____1971 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___152_1970.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1970.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1971
                                } in
                              ((let uu___153_1976 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1976.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___154_1980 = x in
                                let uu____1981 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___154_1980.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___154_1980.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1981
                                } in
                              ((let uu___155_1986 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___155_1986.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___156_1995 = x in
                                let uu____1996 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_1995.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_1995.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1996
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___157_2002 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_2002.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2004 = norm_pat env1 pat in
                        (match uu____2004 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2024 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2024 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2028 =
                    let uu____2029 =
                      let uu____2044 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2044) in
                    FStar_Syntax_Syntax.Tm_match uu____2029 in
                  mk uu____2028 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2091 -> closure_as_term cfg env t
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
        | uu____2107 ->
            FStar_List.map
              (fun uu____2117  ->
                 match uu____2117 with
                 | (x,imp) ->
                     let uu____2132 = closure_as_term_delayed cfg env x in
                     (uu____2132, imp)) args
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
        let uu____2144 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2168  ->
                  fun uu____2169  ->
                    match (uu____2168, uu____2169) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___158_2213 = b in
                          let uu____2214 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___158_2213.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___158_2213.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2214
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2144 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2261 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2273 = closure_as_term_delayed cfg env t in
                 let uu____2274 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2273 uu____2274
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2284 = closure_as_term_delayed cfg env t in
                 let uu____2285 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2284 uu____2285
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
                        (fun uu___134_2301  ->
                           match uu___134_2301 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2305 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2305
                           | f -> f)) in
                 let uu____2309 =
                   let uu___159_2310 = c1 in
                   let uu____2311 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2311;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___159_2310.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2309)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___135_2315  ->
            match uu___135_2315 with
            | FStar_Syntax_Syntax.DECREASES uu____2316 -> false
            | uu____2319 -> true))
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
            let uu____2347 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2347
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2364 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2364
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2390 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2414 =
      let uu____2415 =
        let uu____2421 = FStar_Util.string_of_int i in (uu____2421, None) in
      FStar_Const.Const_int uu____2415 in
    const_as_tm uu____2414 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2448 =
    match uu____2448 with
    | (a,uu____2453) ->
        let uu____2455 =
          let uu____2456 = FStar_Syntax_Subst.compress a in
          uu____2456.FStar_Syntax_Syntax.n in
        (match uu____2455 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2466 = FStar_Util.int_of_string i in Some uu____2466
         | uu____2467 -> None) in
  let arg_as_bounded_int uu____2476 =
    match uu____2476 with
    | (a,uu____2483) ->
        let uu____2487 =
          let uu____2488 = FStar_Syntax_Subst.compress a in
          uu____2488.FStar_Syntax_Syntax.n in
        (match uu____2487 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2495;
                FStar_Syntax_Syntax.pos = uu____2496;
                FStar_Syntax_Syntax.vars = uu____2497;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2499;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2500;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2501;_},uu____2502)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2529 =
               let uu____2532 = FStar_Util.int_of_string i in
               (fv1, uu____2532) in
             Some uu____2529
         | uu____2535 -> None) in
  let arg_as_bool uu____2544 =
    match uu____2544 with
    | (a,uu____2549) ->
        let uu____2551 =
          let uu____2552 = FStar_Syntax_Subst.compress a in
          uu____2552.FStar_Syntax_Syntax.n in
        (match uu____2551 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2557 -> None) in
  let arg_as_char uu____2564 =
    match uu____2564 with
    | (a,uu____2569) ->
        let uu____2571 =
          let uu____2572 = FStar_Syntax_Subst.compress a in
          uu____2572.FStar_Syntax_Syntax.n in
        (match uu____2571 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2577 -> None) in
  let arg_as_string uu____2584 =
    match uu____2584 with
    | (a,uu____2589) ->
        let uu____2591 =
          let uu____2592 = FStar_Syntax_Subst.compress a in
          uu____2592.FStar_Syntax_Syntax.n in
        (match uu____2591 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2597)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2600 -> None) in
  let arg_as_list f uu____2621 =
    match uu____2621 with
    | (a,uu____2630) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2649 -> None
          | (Some x)::xs ->
              let uu____2659 = sequence xs in
              (match uu____2659 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2670 = FStar_Syntax_Util.list_elements a in
        (match uu____2670 with
         | None  -> None
         | Some elts ->
             let uu____2680 =
               FStar_List.map
                 (fun x  ->
                    let uu____2685 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2685) elts in
             sequence uu____2680) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2715 = f a in Some uu____2715
    | uu____2716 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2755 = f a0 a1 in Some uu____2755
    | uu____2756 -> None in
  let unary_op as_a f r args =
    let uu____2800 = FStar_List.map as_a args in lift_unary (f r) uu____2800 in
  let binary_op as_a f r args =
    let uu____2850 = FStar_List.map as_a args in lift_binary (f r) uu____2850 in
  let as_primitive_step uu____2867 =
    match uu____2867 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2905 = f x in int_as_const r uu____2905) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2928 = f x y in int_as_const r uu____2928) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2945 = f x in bool_as_const r uu____2945) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2968 = f x y in bool_as_const r uu____2968) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2991 = f x y in string_as_const r uu____2991) in
  let list_of_string' rng s =
    let name l =
      let uu____3005 =
        let uu____3006 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3006 in
      mk uu____3005 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3016 =
      let uu____3018 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3018 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3016 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3040 = FStar_Util.string_of_int i in
    string_as_const rng uu____3040 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3056 = FStar_Util.string_of_int i in
    string_as_const rng uu____3056 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3075 =
      let uu____3085 =
        let uu____3095 =
          let uu____3105 =
            let uu____3115 =
              let uu____3125 =
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
                                      let uu____3244 =
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
                                      (uu____3244, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3250 =
                                      let uu____3260 =
                                        let uu____3269 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
                                        (uu____3269, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3260] in
                                    uu____3235 :: uu____3250 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3225 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3215 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3205 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3195 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3185 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3175 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3165 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3155 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3145 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3135 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3125 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3115 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3105 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3095 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3085 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3075 in
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
      let uu____3564 =
        let uu____3565 =
          let uu____3566 = FStar_Syntax_Syntax.as_arg c in [uu____3566] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3565 in
      uu____3564 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3590 =
              let uu____3599 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3599, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3608  ->
                        fun uu____3609  ->
                          match (uu____3608, uu____3609) with
                          | ((int_to_t1,x),(uu____3620,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3626 =
              let uu____3636 =
                let uu____3645 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3645, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3654  ->
                          fun uu____3655  ->
                            match (uu____3654, uu____3655) with
                            | ((int_to_t1,x),(uu____3666,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3672 =
                let uu____3682 =
                  let uu____3691 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3691, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3700  ->
                            fun uu____3701  ->
                              match (uu____3700, uu____3701) with
                              | ((int_to_t1,x),(uu____3712,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3682] in
              uu____3636 :: uu____3672 in
            uu____3590 :: uu____3626)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
    | (_typ,uu____3778)::(a1,uu____3780)::(a2,uu____3782)::[] ->
        let uu____3811 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3811 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3813 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3813
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3818 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3818
         | uu____3823 -> None)
    | uu____3824 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3837)::(a1,uu____3839)::(a2,uu____3841)::[] ->
        let uu____3870 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3870 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___160_3874 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_3874.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_3874.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_3874.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___161_3881 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_3881.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_3881.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_3881.FStar_Syntax_Syntax.vars)
                })
         | uu____3886 -> None)
    | (_typ,uu____3888)::uu____3889::(a1,uu____3891)::(a2,uu____3893)::[] ->
        let uu____3930 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3930 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___160_3934 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___160_3934.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___160_3934.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___160_3934.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___161_3941 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_3941.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_3941.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_3941.FStar_Syntax_Syntax.vars)
                })
         | uu____3946 -> None)
    | uu____3947 -> failwith "Unexpected number of arguments" in
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
      let uu____3958 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3958
      then tm
      else
        (let uu____3960 = FStar_Syntax_Util.head_and_args tm in
         match uu____3960 with
         | (head1,args) ->
             let uu____3986 =
               let uu____3987 = FStar_Syntax_Util.un_uinst head1 in
               uu____3987.FStar_Syntax_Syntax.n in
             (match uu____3986 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3991 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3991 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4003 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4003 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4006 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___162_4013 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___162_4013.tcenv);
           delta_level = (uu___162_4013.delta_level);
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
        let uu___163_4035 = t in
        {
          FStar_Syntax_Syntax.n = (uu___163_4035.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___163_4035.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___163_4035.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4054 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4081 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4081
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4084;
                     FStar_Syntax_Syntax.pos = uu____4085;
                     FStar_Syntax_Syntax.vars = uu____4086;_},uu____4087);
                FStar_Syntax_Syntax.tk = uu____4088;
                FStar_Syntax_Syntax.pos = uu____4089;
                FStar_Syntax_Syntax.vars = uu____4090;_},args)
             ->
             let uu____4110 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4110
             then
               let uu____4111 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4111 with
                | (Some (true ),uu____4144)::(uu____4145,(arg,uu____4147))::[]
                    -> arg
                | (uu____4188,(arg,uu____4190))::(Some (true ),uu____4191)::[]
                    -> arg
                | (Some (false ),uu____4232)::uu____4233::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4271::(Some (false ),uu____4272)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4310 -> tm)
             else
               (let uu____4320 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4320
                then
                  let uu____4321 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4321 with
                  | (Some (true ),uu____4354)::uu____4355::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4393::(Some (true ),uu____4394)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4432)::(uu____4433,(arg,uu____4435))::[]
                      -> arg
                  | (uu____4476,(arg,uu____4478))::(Some (false ),uu____4479)::[]
                      -> arg
                  | uu____4520 -> tm
                else
                  (let uu____4530 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4530
                   then
                     let uu____4531 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4531 with
                     | uu____4564::(Some (true ),uu____4565)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4603)::uu____4604::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4642)::(uu____4643,(arg,uu____4645))::[]
                         -> arg
                     | uu____4686 -> tm
                   else
                     (let uu____4696 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4696
                      then
                        let uu____4697 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4697 with
                        | (Some (true ),uu____4730)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4754)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4778 -> tm
                      else
                        (let uu____4788 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4788
                         then
                           match args with
                           | (t,uu____4790)::[] ->
                               let uu____4803 =
                                 let uu____4804 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4804.FStar_Syntax_Syntax.n in
                               (match uu____4803 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4807::[],body,uu____4809) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4835 -> tm)
                                | uu____4837 -> tm)
                           | (uu____4838,Some (FStar_Syntax_Syntax.Implicit
                              uu____4839))::(t,uu____4841)::[] ->
                               let uu____4868 =
                                 let uu____4869 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4869.FStar_Syntax_Syntax.n in
                               (match uu____4868 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4872::[],body,uu____4874) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4900 -> tm)
                                | uu____4902 -> tm)
                           | uu____4903 -> tm
                         else
                           (let uu____4910 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4910
                            then
                              match args with
                              | (t,uu____4912)::[] ->
                                  let uu____4925 =
                                    let uu____4926 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4926.FStar_Syntax_Syntax.n in
                                  (match uu____4925 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4929::[],body,uu____4931) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4957 -> tm)
                                   | uu____4959 -> tm)
                              | (uu____4960,Some
                                 (FStar_Syntax_Syntax.Implicit uu____4961))::
                                  (t,uu____4963)::[] ->
                                  let uu____4990 =
                                    let uu____4991 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4991.FStar_Syntax_Syntax.n in
                                  (match uu____4990 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4994::[],body,uu____4996) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5022 -> tm)
                                   | uu____5024 -> tm)
                              | uu____5025 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5033;
                FStar_Syntax_Syntax.pos = uu____5034;
                FStar_Syntax_Syntax.vars = uu____5035;_},args)
             ->
             let uu____5051 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5051
             then
               let uu____5052 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5052 with
                | (Some (true ),uu____5085)::(uu____5086,(arg,uu____5088))::[]
                    -> arg
                | (uu____5129,(arg,uu____5131))::(Some (true ),uu____5132)::[]
                    -> arg
                | (Some (false ),uu____5173)::uu____5174::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5212::(Some (false ),uu____5213)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5251 -> tm)
             else
               (let uu____5261 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5261
                then
                  let uu____5262 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5262 with
                  | (Some (true ),uu____5295)::uu____5296::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5334::(Some (true ),uu____5335)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5373)::(uu____5374,(arg,uu____5376))::[]
                      -> arg
                  | (uu____5417,(arg,uu____5419))::(Some (false ),uu____5420)::[]
                      -> arg
                  | uu____5461 -> tm
                else
                  (let uu____5471 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5471
                   then
                     let uu____5472 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5472 with
                     | uu____5505::(Some (true ),uu____5506)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5544)::uu____5545::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5583)::(uu____5584,(arg,uu____5586))::[]
                         -> arg
                     | uu____5627 -> tm
                   else
                     (let uu____5637 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5637
                      then
                        let uu____5638 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5638 with
                        | (Some (true ),uu____5671)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5695)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5719 -> tm
                      else
                        (let uu____5729 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5729
                         then
                           match args with
                           | (t,uu____5731)::[] ->
                               let uu____5744 =
                                 let uu____5745 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5745.FStar_Syntax_Syntax.n in
                               (match uu____5744 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5748::[],body,uu____5750) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5776 -> tm)
                                | uu____5778 -> tm)
                           | (uu____5779,Some (FStar_Syntax_Syntax.Implicit
                              uu____5780))::(t,uu____5782)::[] ->
                               let uu____5809 =
                                 let uu____5810 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5810.FStar_Syntax_Syntax.n in
                               (match uu____5809 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5813::[],body,uu____5815) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5841 -> tm)
                                | uu____5843 -> tm)
                           | uu____5844 -> tm
                         else
                           (let uu____5851 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5851
                            then
                              match args with
                              | (t,uu____5853)::[] ->
                                  let uu____5866 =
                                    let uu____5867 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5867.FStar_Syntax_Syntax.n in
                                  (match uu____5866 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5870::[],body,uu____5872) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5898 -> tm)
                                   | uu____5900 -> tm)
                              | (uu____5901,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5902))::
                                  (t,uu____5904)::[] ->
                                  let uu____5931 =
                                    let uu____5932 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5932.FStar_Syntax_Syntax.n in
                                  (match uu____5931 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5935::[],body,uu____5937) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5963 -> tm)
                                   | uu____5965 -> tm)
                              | uu____5966 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5973 -> tm)
let is_norm_request hd1 args =
  let uu____5988 =
    let uu____5992 =
      let uu____5993 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5993.FStar_Syntax_Syntax.n in
    (uu____5992, args) in
  match uu____5988 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5998::uu____5999::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6002::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6004 -> false
let get_norm_request args =
  match args with
  | uu____6023::(tm,uu____6025)::[] -> tm
  | (tm,uu____6035)::[] -> tm
  | uu____6040 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___136_6047  ->
    match uu___136_6047 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6049;
           FStar_Syntax_Syntax.pos = uu____6050;
           FStar_Syntax_Syntax.vars = uu____6051;_},uu____6052,uu____6053))::uu____6054
        -> true
    | uu____6060 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6065 =
      let uu____6066 = FStar_Syntax_Util.un_uinst t in
      uu____6066.FStar_Syntax_Syntax.n in
    match uu____6065 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6070 -> false
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
            (fun uu____6184  ->
               let uu____6185 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6186 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6187 =
                 let uu____6188 =
                   let uu____6190 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6190 in
                 stack_to_string uu____6188 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6185
                 uu____6186 uu____6187);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6202 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_uvar uu____6223 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____6234 =
                 let uu____6235 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____6235 in
               failwith uu____6234
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_uvar uu____6240 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____6255 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____6260 ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6265;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6266;_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6272;
                 FStar_Syntax_Syntax.fv_delta = uu____6273;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6278;
                 FStar_Syntax_Syntax.fv_delta = uu____6279;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6280);_}
               ->
               (FStar_ST.write t1.FStar_Syntax_Syntax.tk None;
                rebuild cfg env stack1 t1)
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6289;
                  FStar_Syntax_Syntax.pos = uu____6290;
                  FStar_Syntax_Syntax.vars = uu____6291;_},uu____6292)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let hd2 = closure_as_term cfg env hd1 in
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___164_6333 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___164_6333.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___164_6333.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___164_6333.FStar_Syntax_Syntax.vars)
                 } in
               (FStar_ST.write t2.FStar_Syntax_Syntax.tk None;
                (let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6364 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6364) && (is_norm_request hd1 args))
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
                 let uu___165_6377 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___165_6377.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___165_6377.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6382;
                  FStar_Syntax_Syntax.pos = uu____6383;
                  FStar_Syntax_Syntax.vars = uu____6384;_},a1::a2::rest)
               ->
               let uu____6418 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6418 with
                | (hd1,uu____6429) ->
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
                    (FStar_Const.Const_reflect uu____6484);
                  FStar_Syntax_Syntax.tk = uu____6485;
                  FStar_Syntax_Syntax.pos = uu____6486;
                  FStar_Syntax_Syntax.vars = uu____6487;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6510 = FStar_List.tl stack1 in
               norm cfg env uu____6510 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6513;
                  FStar_Syntax_Syntax.pos = uu____6514;
                  FStar_Syntax_Syntax.vars = uu____6515;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6538 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6538 with
                | (reify_head,uu____6549) ->
                    let a1 =
                      let uu____6565 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6565 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6568);
                            FStar_Syntax_Syntax.tk = uu____6569;
                            FStar_Syntax_Syntax.pos = uu____6570;
                            FStar_Syntax_Syntax.vars = uu____6571;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6596 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6604 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6604
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6611 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6611
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6614 =
                      let uu____6618 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6618, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6614 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___137_6627  ->
                         match uu___137_6627 with
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
                    let uu____6631 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6631 in
                  let uu____6632 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6632 with
                  | None  ->
                      (log cfg
                         (fun uu____6639  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6645  ->
                            let uu____6646 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6647 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6646 uu____6647);
                       (let t3 =
                          let uu____6649 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6649
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
                          | (UnivArgs (us',uu____6657))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6670 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6671 ->
                              let uu____6672 =
                                let uu____6673 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6673 in
                              failwith uu____6672
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6676 = lookup_bvar env x in
               (match uu____6676 with
                | Univ uu____6677 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6692 = FStar_ST.read r in
                      (match uu____6692 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6711  ->
                                 let uu____6712 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6713 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6712
                                   uu____6713);
                            (let uu____6714 =
                               let uu____6715 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6715.FStar_Syntax_Syntax.n in
                             match uu____6714 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6718 ->
                                 norm cfg env2 stack1 t'
                             | uu____6733 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6766)::uu____6767 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6772)::uu____6773 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6779,uu____6780))::stack_rest ->
                    (match c with
                     | Univ uu____6783 -> norm cfg (c :: env) stack_rest t1
                     | uu____6784 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6787::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6800  ->
                                         let uu____6801 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6801);
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
                                           (fun uu___138_6815  ->
                                              match uu___138_6815 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6816 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6818  ->
                                         let uu____6819 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6819);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____6830  ->
                                         let uu____6831 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6831);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6832 when
                                   (FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains Reify))
                                     ||
                                     (FStar_All.pipe_right cfg.steps
                                        (FStar_List.contains CheckNoUvars))
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6839 ->
                                   let cfg1 =
                                     let uu___166_6847 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___166_6847.tcenv);
                                       delta_level =
                                         (uu___166_6847.delta_level);
                                       primitive_steps =
                                         (uu___166_6847.primitive_steps)
                                     } in
                                   let uu____6848 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6848)
                          | uu____6849::tl1 ->
                              (log cfg
                                 (fun uu____6859  ->
                                    let uu____6860 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6860);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___167_6884 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___167_6884.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6897  ->
                          let uu____6898 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6898);
                     norm cfg env stack2 t1)
                | (Debug uu____6899)::uu____6900 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6902 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6902
                    else
                      (let uu____6904 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6904 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6918  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____6945 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____6945 in
                                 let c1 =
                                   let uu____6947 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____6947
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____6957 -> lopt in
                           (log cfg
                              (fun uu____6965  ->
                                 let uu____6966 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6966);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_6976 = cfg in
                               let uu____6977 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_6976.steps);
                                 tcenv = (uu___168_6976.tcenv);
                                 delta_level = (uu___168_6976.delta_level);
                                 primitive_steps = uu____6977
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6987)::uu____6988 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6992 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6992
                    else
                      (let uu____6994 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6994 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7008  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7035 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7035 in
                                 let c1 =
                                   let uu____7037 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7037
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7047 -> lopt in
                           (log cfg
                              (fun uu____7055  ->
                                 let uu____7056 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7056);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7066 = cfg in
                               let uu____7067 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7066.steps);
                                 tcenv = (uu___168_7066.tcenv);
                                 delta_level = (uu___168_7066.delta_level);
                                 primitive_steps = uu____7067
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7077)::uu____7078 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7084 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7084
                    else
                      (let uu____7086 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7086 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7100  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7127 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7127 in
                                 let c1 =
                                   let uu____7129 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7129
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7139 -> lopt in
                           (log cfg
                              (fun uu____7147  ->
                                 let uu____7148 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7148);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7158 = cfg in
                               let uu____7159 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7158.steps);
                                 tcenv = (uu___168_7158.tcenv);
                                 delta_level = (uu___168_7158.delta_level);
                                 primitive_steps = uu____7159
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7169)::uu____7170 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7175 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7175
                    else
                      (let uu____7177 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7177 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7191  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7218 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7218 in
                                 let c1 =
                                   let uu____7220 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7220
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7230 -> lopt in
                           (log cfg
                              (fun uu____7238  ->
                                 let uu____7239 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7239);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7249 = cfg in
                               let uu____7250 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7249.steps);
                                 tcenv = (uu___168_7249.tcenv);
                                 delta_level = (uu___168_7249.delta_level);
                                 primitive_steps = uu____7250
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7260)::uu____7261 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7271 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7271
                    else
                      (let uu____7273 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7273 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7287  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7314 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7314 in
                                 let c1 =
                                   let uu____7316 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7316
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7326 -> lopt in
                           (log cfg
                              (fun uu____7334  ->
                                 let uu____7335 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7335);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7345 = cfg in
                               let uu____7346 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7345.steps);
                                 tcenv = (uu___168_7345.tcenv);
                                 delta_level = (uu___168_7345.delta_level);
                                 primitive_steps = uu____7346
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7356 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7356
                    else
                      (let uu____7358 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7358 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7372  -> Dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let c =
                                   let uu____7399 =
                                     l.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Subst.subst_comp opening
                                     uu____7399 in
                                 let c1 =
                                   let uu____7401 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____7401
                                   then norm_comp cfg env' c
                                   else c in
                                 Some
                                   (FStar_Util.Inl
                                      (FStar_Syntax_Util.lcomp_of_comp c1))
                             | uu____7411 -> lopt in
                           (log cfg
                              (fun uu____7419  ->
                                 let uu____7420 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7420);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___168_7430 = cfg in
                               let uu____7431 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___168_7430.steps);
                                 tcenv = (uu___168_7430.tcenv);
                                 delta_level = (uu___168_7430.delta_level);
                                 primitive_steps = uu____7431
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
                      (fun uu____7463  ->
                         fun stack2  ->
                           match uu____7463 with
                           | (a,aq) ->
                               let uu____7471 =
                                 let uu____7472 =
                                   let uu____7476 =
                                     let uu____7477 =
                                       let uu____7487 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7487, false) in
                                     Clos uu____7477 in
                                   (uu____7476, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7472 in
                               uu____7471 :: stack2) args) in
               (log cfg
                  (fun uu____7509  ->
                     let uu____7510 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7510);
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
                             ((let uu___169_7531 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___169_7531.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___169_7531.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7532 ->
                      let uu____7535 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7535)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7538 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7538 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7554 =
                          let uu____7555 =
                            let uu____7560 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___170_7561 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_7561.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___170_7561.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7560) in
                          FStar_Syntax_Syntax.Tm_refine uu____7555 in
                        mk uu____7554 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7574 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7574
               else
                 (let uu____7576 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7576 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7582 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7588  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7582 c1 in
                      let t2 =
                        let uu____7595 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7595 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7638)::uu____7639 -> norm cfg env stack1 t11
                | (Arg uu____7644)::uu____7645 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7650;
                       FStar_Syntax_Syntax.pos = uu____7651;
                       FStar_Syntax_Syntax.vars = uu____7652;_},uu____7653,uu____7654))::uu____7655
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7661)::uu____7662 ->
                    norm cfg env stack1 t11
                | uu____7667 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7670  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7683 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7683
                        | FStar_Util.Inr c ->
                            let uu____7691 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7691 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7696 =
                        let uu____7697 =
                          let uu____7698 =
                            let uu____7716 = FStar_Syntax_Util.unascribe t12 in
                            (uu____7716, (tc1, tacopt1), l) in
                          FStar_Syntax_Syntax.Tm_ascribed uu____7698 in
                        mk uu____7697 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____7696)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7764,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7765;
                              FStar_Syntax_Syntax.lbunivs = uu____7766;
                              FStar_Syntax_Syntax.lbtyp = uu____7767;
                              FStar_Syntax_Syntax.lbeff = uu____7768;
                              FStar_Syntax_Syntax.lbdef = uu____7769;_}::uu____7770),uu____7771)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____7797 =
                 (let uu____7798 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7798) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7799 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7799))) in
               if uu____7797
               then
                 let env1 =
                   let uu____7802 =
                     let uu____7803 =
                       let uu____7813 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7813,
                         false) in
                     Clos uu____7803 in
                   uu____7802 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7837 =
                    let uu____7840 =
                      let uu____7841 =
                        let uu____7842 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7842
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7841] in
                    FStar_Syntax_Subst.open_term uu____7840 body in
                  match uu____7837 with
                  | (bs,body1) ->
                      let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                      let lbname =
                        let x =
                          let uu____7852 = FStar_List.hd bs in fst uu____7852 in
                        FStar_Util.Inl
                          (let uu___171_7857 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___171_7857.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___171_7857.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = ty
                           }) in
                      let lb1 =
                        let uu___172_7859 = lb in
                        let uu____7860 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = lbname;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_7859.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = ty;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_7859.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7860
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7870  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               FStar_List.contains CompressUvars cfg.steps ->
               let uu____7885 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____7885 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____7900 =
                               let uu___173_7901 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___173_7901.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___173_7901.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____7900 in
                           let uu____7902 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____7902 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____7930 =
                                   FStar_List.map (fun uu____7932  -> Dummy)
                                     lbs1 in
                                 let uu____7933 =
                                   let uu____7935 =
                                     FStar_List.map
                                       (fun uu____7939  -> Dummy) xs1 in
                                   FStar_List.append uu____7935 env in
                                 FStar_List.append uu____7930 uu____7933 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 None in
                               let uu___174_7949 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___174_7949.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___174_7949.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____7952 =
                        FStar_List.map (fun uu____7954  -> Dummy) lbs2 in
                      FStar_List.append uu____7952 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____7956 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____7956 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___175_7967 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.tk =
                               (uu___175_7967.FStar_Syntax_Syntax.tk);
                             FStar_Syntax_Syntax.pos =
                               (uu___175_7967.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___175_7967.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7988 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7988
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8001 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8023  ->
                        match uu____8023 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8062 =
                                let uu___176_8063 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___176_8063.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___176_8063.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8062 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8001 with
                | (rec_env,memos,uu____8123) ->
                    let uu____8138 =
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
                             let uu____8180 =
                               let uu____8181 =
                                 let uu____8191 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8191, false) in
                               Clos uu____8181 in
                             uu____8180 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8229;
                             FStar_Syntax_Syntax.pos = uu____8230;
                             FStar_Syntax_Syntax.vars = uu____8231;_},uu____8232,uu____8233))::uu____8234
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8240 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8247 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8247
                        then
                          let uu___177_8248 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___177_8248.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___177_8248.primitive_steps)
                          }
                        else
                          (let uu___178_8250 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___178_8250.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___178_8250.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8252 =
                         let uu____8253 = FStar_Syntax_Subst.compress head1 in
                         uu____8253.FStar_Syntax_Syntax.n in
                       match uu____8252 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8267 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8267 with
                            | (uu____8268,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8272 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8279 =
                                         let uu____8280 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8280.FStar_Syntax_Syntax.n in
                                       match uu____8279 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8285,uu____8286))
                                           ->
                                           let uu____8295 =
                                             let uu____8296 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8296.FStar_Syntax_Syntax.n in
                                           (match uu____8295 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8301,msrc,uu____8303))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8312 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8312
                                            | uu____8313 -> None)
                                       | uu____8314 -> None in
                                     let uu____8315 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8315 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___179_8319 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___179_8319.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___179_8319.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___179_8319.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8320 =
                                            FStar_List.tl stack1 in
                                          let uu____8321 =
                                            let uu____8322 =
                                              let uu____8325 =
                                                let uu____8326 =
                                                  let uu____8334 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8334) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8326 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8325 in
                                            uu____8322 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8320 uu____8321
                                      | None  ->
                                          let uu____8351 =
                                            let uu____8352 = is_return body in
                                            match uu____8352 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8355;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8356;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8357;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8362 -> false in
                                          if uu____8351
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
                                               let uu____8382 =
                                                 let uu____8385 =
                                                   let uu____8386 =
                                                     let uu____8401 =
                                                       let uu____8403 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8403] in
                                                     (uu____8401, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8386 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8385 in
                                               uu____8382 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8436 =
                                                 let uu____8437 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8437.FStar_Syntax_Syntax.n in
                                               match uu____8436 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8443::uu____8444::[])
                                                   ->
                                                   let uu____8450 =
                                                     let uu____8453 =
                                                       let uu____8454 =
                                                         let uu____8459 =
                                                           let uu____8461 =
                                                             let uu____8462 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8462 in
                                                           let uu____8463 =
                                                             let uu____8465 =
                                                               let uu____8466
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8466 in
                                                             [uu____8465] in
                                                           uu____8461 ::
                                                             uu____8463 in
                                                         (bind1, uu____8459) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8454 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8453 in
                                                   uu____8450 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8478 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8484 =
                                                 let uu____8487 =
                                                   let uu____8488 =
                                                     let uu____8498 =
                                                       let uu____8500 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8501 =
                                                         let uu____8503 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8504 =
                                                           let uu____8506 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8507 =
                                                             let uu____8509 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8510 =
                                                               let uu____8512
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8513
                                                                 =
                                                                 let uu____8515
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8515] in
                                                               uu____8512 ::
                                                                 uu____8513 in
                                                             uu____8509 ::
                                                               uu____8510 in
                                                           uu____8506 ::
                                                             uu____8507 in
                                                         uu____8503 ::
                                                           uu____8504 in
                                                       uu____8500 ::
                                                         uu____8501 in
                                                     (bind_inst, uu____8498) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8488 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8487 in
                                               uu____8484 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8527 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8527 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8545 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8545 with
                            | (uu____8546,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8569 =
                                        let uu____8570 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8570.FStar_Syntax_Syntax.n in
                                      match uu____8569 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8576) -> t4
                                      | uu____8581 -> head2 in
                                    let uu____8582 =
                                      let uu____8583 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8583.FStar_Syntax_Syntax.n in
                                    match uu____8582 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8588 -> None in
                                  let uu____8589 = maybe_extract_fv head2 in
                                  match uu____8589 with
                                  | Some x when
                                      let uu____8595 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8595
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8599 =
                                          maybe_extract_fv head3 in
                                        match uu____8599 with
                                        | Some uu____8602 -> Some true
                                        | uu____8603 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8606 -> (head2, None) in
                                ((let is_arg_impure uu____8617 =
                                    match uu____8617 with
                                    | (e,q) ->
                                        let uu____8622 =
                                          let uu____8623 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8623.FStar_Syntax_Syntax.n in
                                        (match uu____8622 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8638 -> false) in
                                  let uu____8639 =
                                    let uu____8640 =
                                      let uu____8644 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8644 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8640 in
                                  if uu____8639
                                  then
                                    let uu____8647 =
                                      let uu____8648 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8648 in
                                    failwith uu____8647
                                  else ());
                                 (let uu____8650 =
                                    maybe_unfold_action head_app in
                                  match uu____8650 with
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
                                      let uu____8685 = FStar_List.tl stack1 in
                                      norm cfg env uu____8685 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8699 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8699 in
                           let uu____8700 = FStar_List.tl stack1 in
                           norm cfg env uu____8700 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8776  ->
                                     match uu____8776 with
                                     | (pat,wopt,tm) ->
                                         let uu____8810 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8810))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8834 = FStar_List.tl stack1 in
                           norm cfg env uu____8834 tm
                       | uu____8835 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8844;
                             FStar_Syntax_Syntax.pos = uu____8845;
                             FStar_Syntax_Syntax.vars = uu____8846;_},uu____8847,uu____8848))::uu____8849
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8855 -> false in
                    if should_reify
                    then
                      let uu____8856 = FStar_List.tl stack1 in
                      let uu____8857 =
                        let uu____8858 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8858 in
                      norm cfg env uu____8856 uu____8857
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8861 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____8861
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___180_8867 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___180_8867.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___180_8867.primitive_steps)
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
                | uu____8869 ->
                    (match stack1 with
                     | uu____8870::uu____8871 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8875)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8890 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8900 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8900
                           | uu____8907 -> m in
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
              let uu____8919 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8919 with
              | (uu____8920,return_repr) ->
                  let return_inst =
                    let uu____8927 =
                      let uu____8928 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8928.FStar_Syntax_Syntax.n in
                    match uu____8927 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8934::[])
                        ->
                        let uu____8940 =
                          let uu____8943 =
                            let uu____8944 =
                              let uu____8949 =
                                let uu____8951 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8951] in
                              (return_tm, uu____8949) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8944 in
                          FStar_Syntax_Syntax.mk uu____8943 in
                        uu____8940 None e.FStar_Syntax_Syntax.pos
                    | uu____8963 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8966 =
                    let uu____8969 =
                      let uu____8970 =
                        let uu____8980 =
                          let uu____8982 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8983 =
                            let uu____8985 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8985] in
                          uu____8982 :: uu____8983 in
                        (return_inst, uu____8980) in
                      FStar_Syntax_Syntax.Tm_app uu____8970 in
                    FStar_Syntax_Syntax.mk uu____8969 in
                  uu____8966 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8998 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8998 with
               | None  ->
                   let uu____9000 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9000
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9001;
                     FStar_TypeChecker_Env.mtarget = uu____9002;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9003;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9014;
                     FStar_TypeChecker_Env.mtarget = uu____9015;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9016;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9034 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9034)
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
                (fun uu____9064  ->
                   match uu____9064 with
                   | (a,imp) ->
                       let uu____9071 = norm cfg env [] a in
                       (uu____9071, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___181_9086 = comp1 in
            let uu____9089 =
              let uu____9090 =
                let uu____9096 = norm cfg env [] t in
                let uu____9097 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9096, uu____9097) in
              FStar_Syntax_Syntax.Total uu____9090 in
            {
              FStar_Syntax_Syntax.n = uu____9089;
              FStar_Syntax_Syntax.tk = (uu___181_9086.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___181_9086.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___181_9086.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___182_9112 = comp1 in
            let uu____9115 =
              let uu____9116 =
                let uu____9122 = norm cfg env [] t in
                let uu____9123 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9122, uu____9123) in
              FStar_Syntax_Syntax.GTotal uu____9116 in
            {
              FStar_Syntax_Syntax.n = uu____9115;
              FStar_Syntax_Syntax.tk = (uu___182_9112.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___182_9112.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___182_9112.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9154  ->
                      match uu____9154 with
                      | (a,i) ->
                          let uu____9161 = norm cfg env [] a in
                          (uu____9161, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___139_9166  ->
                      match uu___139_9166 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9170 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9170
                      | f -> f)) in
            let uu___183_9174 = comp1 in
            let uu____9177 =
              let uu____9178 =
                let uu___184_9179 = ct in
                let uu____9180 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9181 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9184 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9180;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___184_9179.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9181;
                  FStar_Syntax_Syntax.effect_args = uu____9184;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9178 in
            {
              FStar_Syntax_Syntax.n = uu____9177;
              FStar_Syntax_Syntax.tk = (uu___183_9174.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9174.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9174.FStar_Syntax_Syntax.vars)
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
            (let uu___185_9201 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___185_9201.tcenv);
               delta_level = (uu___185_9201.delta_level);
               primitive_steps = (uu___185_9201.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9206 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9206 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9209 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___186_9223 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___186_9223.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___186_9223.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_9223.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9233 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9233
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___187_9238 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___187_9238.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___187_9238.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___187_9238.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___187_9238.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___188_9240 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___188_9240.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___188_9240.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___188_9240.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___188_9240.FStar_Syntax_Syntax.flags)
                    } in
              let uu___189_9241 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___189_9241.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___189_9241.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___189_9241.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9247 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9250  ->
        match uu____9250 with
        | (x,imp) ->
            let uu____9253 =
              let uu___190_9254 = x in
              let uu____9255 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___190_9254.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___190_9254.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9255
              } in
            (uu____9253, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9261 =
          FStar_List.fold_left
            (fun uu____9268  ->
               fun b  ->
                 match uu____9268 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9261 with | (nbs,uu____9285) -> FStar_List.rev nbs
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
            let uu____9302 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9302
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9307 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9307
               then
                 let uu____9311 =
                   let uu____9314 =
                     let uu____9315 =
                       let uu____9318 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9318 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9315 in
                   FStar_Util.Inl uu____9314 in
                 Some uu____9311
               else
                 (let uu____9322 =
                    let uu____9325 =
                      let uu____9326 =
                        let uu____9329 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9329 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9326 in
                    FStar_Util.Inl uu____9325 in
                  Some uu____9322))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9342 -> lopt
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
              ((let uu____9354 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9354
                then
                  let uu____9355 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9356 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9355
                    uu____9356
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___191_9367 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___191_9367.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9387  ->
                    let uu____9388 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9388);
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
              let uu____9425 =
                let uu___192_9426 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___192_9426.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___192_9426.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___192_9426.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9425
          | (Arg (Univ uu____9431,uu____9432,uu____9433))::uu____9434 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9436,uu____9437))::uu____9438 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9450),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9466  ->
                    let uu____9467 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9467);
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
                 (let uu____9478 = FStar_ST.read m in
                  match uu____9478 with
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
                  | Some (uu____9504,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9526 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9526
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9533  ->
                    let uu____9534 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9534);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9539 =
                  log cfg
                    (fun uu____9541  ->
                       let uu____9542 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9543 =
                         let uu____9544 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9551  ->
                                   match uu____9551 with
                                   | (p,uu____9557,uu____9558) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9544
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9542 uu____9543);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___140_9568  ->
                               match uu___140_9568 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9569 -> false)) in
                     let steps' =
                       let uu____9572 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9572
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___193_9575 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___193_9575.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___193_9575.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9605 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9618 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9647  ->
                                   fun uu____9648  ->
                                     match (uu____9647, uu____9648) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9702 = norm_pat env3 p1 in
                                         (match uu____9702 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9618 with
                          | (pats1,env3) ->
                              ((let uu___194_9755 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.p =
                                    (uu___194_9755.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___195_9766 = x in
                           let uu____9767 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___195_9766.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___195_9766.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9767
                           } in
                         ((let uu___196_9772 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.p =
                               (uu___196_9772.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___197_9776 = x in
                           let uu____9777 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___197_9776.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___197_9776.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9777
                           } in
                         ((let uu___198_9782 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.p =
                               (uu___198_9782.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___199_9791 = x in
                           let uu____9792 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___199_9791.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___199_9791.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9792
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___200_9798 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.p =
                               (uu___200_9798.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9801 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9804 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9804 with
                                 | (p,wopt,e) ->
                                     let uu____9820 = norm_pat env1 p in
                                     (match uu____9820 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9841 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9841 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9845 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9845) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9855) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9860 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9861;
                        FStar_Syntax_Syntax.fv_delta = uu____9862;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9863;
                        FStar_Syntax_Syntax.fv_delta = uu____9864;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9865);_}
                      -> true
                  | uu____9869 -> false in
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
                  let uu____9965 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____9965 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____9997 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____9999 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10001 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10013 ->
                                let uu____10014 =
                                  let uu____10015 = is_cons head1 in
                                  Prims.op_Negation uu____10015 in
                                FStar_Util.Inr uu____10014)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10027 =
                             let uu____10028 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10028.FStar_Syntax_Syntax.n in
                           (match uu____10027 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10035 ->
                                let uu____10036 =
                                  let uu____10037 = is_cons head1 in
                                  Prims.op_Negation uu____10037 in
                                FStar_Util.Inr uu____10036))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10071)::rest_a,(p1,uu____10074)::rest_p) ->
                      let uu____10102 = matches_pat t1 p1 in
                      (match uu____10102 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10116 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10187 = matches_pat scrutinee1 p1 in
                      (match uu____10187 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10197  ->
                                 let uu____10198 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10199 =
                                   let uu____10200 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10200
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10198 uu____10199);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10209 =
                                        let uu____10210 =
                                          let uu____10220 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10220, false) in
                                        Clos uu____10210 in
                                      uu____10209 :: env2) env1 s in
                             let uu____10243 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10243))) in
                let uu____10244 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10244
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___141_10258  ->
                match uu___141_10258 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____10261 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10265 -> d in
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
            let uu___201_10285 = config s e in
            {
              steps = (uu___201_10285.steps);
              tcenv = (uu___201_10285.tcenv);
              delta_level = (uu___201_10285.delta_level);
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
      fun t  -> let uu____10304 = config s e in norm_comp uu____10304 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10311 = config [] env in norm_universe uu____10311 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10318 = config [] env in ghost_to_pure_aux uu____10318 [] c
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
        let uu____10330 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10330 in
      let uu____10331 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10331
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___202_10333 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___202_10333.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___202_10333.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10334  ->
                    let uu____10335 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10335))
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
            ((let uu____10348 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10348);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10357 = config [AllowUnboundUniverses] env in
          norm_comp uu____10357 [] c
        with
        | e ->
            ((let uu____10361 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10361);
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
                   let uu____10398 =
                     let uu____10399 =
                       let uu____10404 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10404) in
                     FStar_Syntax_Syntax.Tm_refine uu____10399 in
                   mk uu____10398 t01.FStar_Syntax_Syntax.pos
               | uu____10409 -> t2)
          | uu____10410 -> t2 in
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
        let uu____10449 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10449 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10465 ->
                 let uu____10469 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10469 with
                  | (actuals,uu____10480,uu____10481) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10503 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10503 with
                         | (binders,args) ->
                             let uu____10513 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10516 =
                               let uu____10523 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_32  -> FStar_Util.Inl _0_32) in
                               FStar_All.pipe_right uu____10523
                                 (fun _0_33  -> Some _0_33) in
                             FStar_Syntax_Util.abs binders uu____10513
                               uu____10516)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10559 =
        let uu____10563 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10563, (t.FStar_Syntax_Syntax.n)) in
      match uu____10559 with
      | (Some sort,uu____10570) ->
          let uu____10572 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10572
      | (uu____10573,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10577 ->
          let uu____10581 = FStar_Syntax_Util.head_and_args t in
          (match uu____10581 with
           | (head1,args) ->
               let uu____10607 =
                 let uu____10608 = FStar_Syntax_Subst.compress head1 in
                 uu____10608.FStar_Syntax_Syntax.n in
               (match uu____10607 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10611,thead) ->
                    let uu____10629 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10629 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10660 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___207_10664 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___207_10664.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___207_10664.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___207_10664.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___207_10664.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___207_10664.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___207_10664.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___207_10664.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___207_10664.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___207_10664.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___207_10664.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___207_10664.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___207_10664.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___207_10664.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___207_10664.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___207_10664.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___207_10664.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___207_10664.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___207_10664.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___207_10664.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___207_10664.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___207_10664.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____10660 with
                            | (uu____10665,ty,uu____10667) ->
                                eta_expand_with_type env t ty))
                | uu____10668 ->
                    let uu____10669 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___208_10673 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___208_10673.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___208_10673.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___208_10673.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___208_10673.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___208_10673.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___208_10673.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___208_10673.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___208_10673.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___208_10673.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___208_10673.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___208_10673.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___208_10673.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___208_10673.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___208_10673.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___208_10673.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___208_10673.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___208_10673.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___208_10673.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___208_10673.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___208_10673.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___208_10673.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____10669 with
                     | (uu____10674,ty,uu____10676) ->
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
            | (uu____10722,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c)) None
                  c.FStar_Syntax_Syntax.pos
            | (uu____10730,FStar_Util.Inl t) ->
                let uu____10734 =
                  let uu____10737 =
                    let uu____10738 =
                      let uu____10746 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____10746) in
                    FStar_Syntax_Syntax.Tm_arrow uu____10738 in
                  FStar_Syntax_Syntax.mk uu____10737 in
                uu____10734 None t.FStar_Syntax_Syntax.pos in
          let uu____10755 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____10755 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____10772 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____10804 ->
                    let uu____10805 =
                      let uu____10810 =
                        let uu____10811 = FStar_Syntax_Subst.compress t3 in
                        uu____10811.FStar_Syntax_Syntax.n in
                      (uu____10810, tc) in
                    (match uu____10805 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____10827) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____10851) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____10877,FStar_Util.Inl uu____10878) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____10892 -> failwith "Impossible") in
              (match uu____10772 with
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
          let uu____10957 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____10957 with
          | (univ_names1,binders1,tc) ->
              let uu____10991 = FStar_Util.left tc in
              (univ_names1, binders1, uu____10991)
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
          let uu____11017 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____11017 with
          | (univ_names1,binders1,tc) ->
              let uu____11053 = FStar_Util.right tc in
              (univ_names1, binders1, uu____11053)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____11079 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____11079 with
           | (univ_names1,binders1,typ1) ->
               let uu___209_11095 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_11095.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_11095.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_11095.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___210_11107 = s in
          let uu____11108 =
            let uu____11109 =
              let uu____11114 = FStar_List.map (elim_uvars env) sigs in
              (uu____11114, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____11109 in
          {
            FStar_Syntax_Syntax.sigel = uu____11108;
            FStar_Syntax_Syntax.sigrng =
              (uu___210_11107.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_11107.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_11107.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____11126 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11126 with
           | (univ_names1,uu____11136,typ1) ->
               let uu___211_11144 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_11144.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_11144.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_11144.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____11149 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11149 with
           | (univ_names1,uu____11159,typ1) ->
               let uu___212_11167 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___212_11167.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___212_11167.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___212_11167.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids,attrs) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____11186 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____11186 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____11201 =
                            let uu____11202 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____11202 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____11201 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___213_11205 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___213_11205.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___213_11205.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___214_11206 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids, attrs));
            FStar_Syntax_Syntax.sigrng =
              (uu___214_11206.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_11206.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_11206.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___215_11214 = s in
          let uu____11215 =
            let uu____11216 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____11216 in
          {
            FStar_Syntax_Syntax.sigel = uu____11215;
            FStar_Syntax_Syntax.sigrng =
              (uu___215_11214.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___215_11214.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___215_11214.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____11220 = elim_uvars_aux_t env us [] t in
          (match uu____11220 with
           | (us1,uu____11230,t1) ->
               let uu___216_11238 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_11238.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_11238.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_11238.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11239 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11241 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____11241 with
           | (univs1,binders,signature) ->
               let uu____11257 =
                 let uu____11262 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____11262 with
                 | (univs_opening,univs2) ->
                     let uu____11277 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____11277) in
               (match uu____11257 with
                | (univs_opening,univs_closing) ->
                    let uu____11287 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____11291 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____11292 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____11291, uu____11292) in
                    (match uu____11287 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____11309 =
                           match uu____11309 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____11321 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____11321 with
                                | (us1,t1) ->
                                    let uu____11328 =
                                      let uu____11331 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____11335 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____11331, uu____11335) in
                                    (match uu____11328 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____11343 =
                                           let uu____11346 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____11351 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____11346, uu____11351) in
                                         (match uu____11343 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____11361 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____11361 in
                                              let uu____11362 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____11362 with
                                               | (uu____11373,uu____11374,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____11383 =
                                                       let uu____11384 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____11384 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____11383 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____11389 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____11389 with
                           | (uu____11396,uu____11397,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_ascribed
                                   ((a.FStar_Syntax_Syntax.action_defn),
                                     ((FStar_Util.Inl
                                         (a.FStar_Syntax_Syntax.action_typ)),
                                       None), None))) None
                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_typ_templ t =
                             let uu____11451 =
                               let uu____11452 =
                                 FStar_Syntax_Subst.compress t in
                               uu____11452.FStar_Syntax_Syntax.n in
                             match uu____11451 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl typ,None ),None ) ->
                                 (defn, typ)
                             | uu____11500 -> failwith "Impossible" in
                           let uu____11507 =
                             elim_uvars_aux_t env
                               (FStar_List.append univs1
                                  a.FStar_Syntax_Syntax.action_univs)
                               (FStar_List.append binders
                                  a.FStar_Syntax_Syntax.action_params)
                               action_typ_templ in
                           match uu____11507 with
                           | (u_action_univs,b_action_params,res) ->
                               let action_univs =
                                 FStar_Util.nth_tail n1 u_action_univs in
                               let action_params =
                                 FStar_Util.nth_tail
                                   (FStar_List.length binders)
                                   b_action_params in
                               let uu____11539 =
                                 destruct_action_typ_templ res in
                               (match uu____11539 with
                                | (action_defn,action_typ) ->
                                    let uu___217_11556 = a in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        (uu___217_11556.FStar_Syntax_Syntax.action_name);
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (uu___217_11556.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___218_11558 = ed in
                           let uu____11559 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____11560 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____11561 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____11562 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____11563 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____11564 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____11565 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____11566 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____11567 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____11568 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____11569 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____11570 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____11571 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____11572 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___218_11558.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___218_11558.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____11559;
                             FStar_Syntax_Syntax.bind_wp = uu____11560;
                             FStar_Syntax_Syntax.if_then_else = uu____11561;
                             FStar_Syntax_Syntax.ite_wp = uu____11562;
                             FStar_Syntax_Syntax.stronger = uu____11563;
                             FStar_Syntax_Syntax.close_wp = uu____11564;
                             FStar_Syntax_Syntax.assert_p = uu____11565;
                             FStar_Syntax_Syntax.assume_p = uu____11566;
                             FStar_Syntax_Syntax.null_wp = uu____11567;
                             FStar_Syntax_Syntax.trivial = uu____11568;
                             FStar_Syntax_Syntax.repr = uu____11569;
                             FStar_Syntax_Syntax.return_repr = uu____11570;
                             FStar_Syntax_Syntax.bind_repr = uu____11571;
                             FStar_Syntax_Syntax.actions = uu____11572
                           } in
                         let uu___219_11574 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___219_11574.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___219_11574.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___219_11574.FStar_Syntax_Syntax.sigmeta)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___142_11585 =
            match uu___142_11585 with
            | None  -> None
            | Some (us,t) ->
                let uu____11600 = elim_uvars_aux_t env us [] t in
                (match uu____11600 with
                 | (us1,uu____11613,t1) -> Some (us1, t1)) in
          let sub_eff1 =
            let uu___220_11624 = sub_eff in
            let uu____11625 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____11627 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___220_11624.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___220_11624.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____11625;
              FStar_Syntax_Syntax.lift = uu____11627
            } in
          let uu___221_11629 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___221_11629.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___221_11629.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___221_11629.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____11637 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____11637 with
           | (univ_names1,binders1,comp1) ->
               let uu___222_11659 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_11659.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_11659.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_11659.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____11666 -> s