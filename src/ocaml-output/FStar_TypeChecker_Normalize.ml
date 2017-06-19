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
  fun projectee  -> match projectee with | Beta  -> true | uu____13 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____18 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____23 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____29 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_WHNF: step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____42 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____47 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____52 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____57 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____62 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____68 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____81 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____86 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____91 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____96 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____101 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____106 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____111 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____116 -> false
type steps = step Prims.list
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option;}
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__interpretation:
  primitive_step ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type closure =
  | Clos of (closure Prims.list* FStar_Syntax_Syntax.term* (closure
  Prims.list* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo*
  Prims.bool)
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____238 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____279 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____292 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___135_297  ->
    match uu___135_297 with
    | Clos (uu____298,t,uu____300,uu____301) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____312 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps;_} ->
        __fname__primitive_steps
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
    match projectee with | Arg _0 -> true | uu____464 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____490 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____516 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____545 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____576 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____617 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____642 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____666 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____697 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____726 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____782 = FStar_ST.read r in
  match uu____782 with
  | Some uu____787 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____797 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____797 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___136_803  ->
    match uu___136_803 with
    | Arg (c,uu____805,uu____806) ->
        let uu____807 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____807
    | MemoLazy uu____808 -> "MemoLazy"
    | Abs (uu____812,bs,uu____814,uu____815,uu____816) ->
        let uu____823 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____823
    | UnivArgs uu____830 -> "UnivArgs"
    | Match uu____834 -> "Match"
    | App (t,uu____839,uu____840) ->
        let uu____841 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____841
    | Meta (m,uu____843) -> "Meta"
    | Let uu____844 -> "Let"
    | Steps (uu____849,uu____850,uu____851) -> "Steps"
    | Debug t ->
        let uu____857 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____857
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____864 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____864 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____880 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____880 then f () else ()
let is_empty uu___137_891 =
  match uu___137_891 with | [] -> true | uu____893 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____914 ->
      let uu____915 =
        let uu____916 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____916 in
      failwith uu____915
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
          let uu____951 =
            FStar_List.fold_left
              (fun uu____960  ->
                 fun u1  ->
                   match uu____960 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____975 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____975 with
                        | (k_u,n1) ->
                            let uu____984 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____984
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____951 with
          | (uu____994,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1010 = FStar_List.nth env x in
                 match uu____1010 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1013 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1017 ->
                   let uu____1018 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1018
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1022 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1025 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1030 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1030 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1041 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1041 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1046 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1049 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1049 with
                                  | (uu____1052,m) -> n1 <= m)) in
                        if uu____1046 then rest1 else us1
                    | uu____1056 -> us1)
               | uu____1059 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1062 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1062 in
        let uu____1064 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1064
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1066 = aux u in
           match uu____1066 with
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
          (fun uu____1163  ->
             let uu____1164 = FStar_Syntax_Print.tag_of_term t in
             let uu____1165 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1164
               uu____1165);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1166 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1169 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1190 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1191 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1192 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1193 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1203 =
                    let uu____1204 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1204 in
                  mk uu____1203 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1211 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1211
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1213 = lookup_bvar env x in
                  (match uu____1213 with
                   | Univ uu____1214 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1218) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1286 = closures_as_binders_delayed cfg env bs in
                  (match uu____1286 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1306 =
                         let uu____1307 =
                           let uu____1322 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1322) in
                         FStar_Syntax_Syntax.Tm_abs uu____1307 in
                       mk uu____1306 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1352 = closures_as_binders_delayed cfg env bs in
                  (match uu____1352 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1383 =
                    let uu____1390 =
                      let uu____1394 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1394] in
                    closures_as_binders_delayed cfg env uu____1390 in
                  (match uu____1383 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1408 =
                         let uu____1409 =
                           let uu____1414 =
                             let uu____1415 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1415
                               FStar_Pervasives.fst in
                           (uu____1414, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1409 in
                       mk uu____1408 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1483 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1483
                    | FStar_Util.Inr c ->
                        let uu____1497 = close_comp cfg env c in
                        FStar_Util.Inr uu____1497 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1512 =
                    let uu____1513 =
                      let uu____1531 = closure_as_term_delayed cfg env t11 in
                      (uu____1531, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1513 in
                  mk uu____1512 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1569 =
                    let uu____1570 =
                      let uu____1575 = closure_as_term_delayed cfg env t' in
                      let uu____1578 =
                        let uu____1579 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1579 in
                      (uu____1575, uu____1578) in
                    FStar_Syntax_Syntax.Tm_meta uu____1570 in
                  mk uu____1569 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1621 =
                    let uu____1622 =
                      let uu____1627 = closure_as_term_delayed cfg env t' in
                      let uu____1630 =
                        let uu____1631 =
                          let uu____1636 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1636) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1631 in
                      (uu____1627, uu____1630) in
                    FStar_Syntax_Syntax.Tm_meta uu____1622 in
                  mk uu____1621 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1655 =
                    let uu____1656 =
                      let uu____1661 = closure_as_term_delayed cfg env t' in
                      let uu____1664 =
                        let uu____1665 =
                          let uu____1671 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1671) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1665 in
                      (uu____1661, uu____1664) in
                    FStar_Syntax_Syntax.Tm_meta uu____1656 in
                  mk uu____1655 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1684 =
                    let uu____1685 =
                      let uu____1690 = closure_as_term_delayed cfg env t' in
                      (uu____1690, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1685 in
                  mk uu____1684 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1711  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1722 -> body
                    | FStar_Util.Inl uu____1723 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___150_1725 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1725.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1725.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1725.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1732,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1756  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1761 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1761
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1765  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___151_1768 = lb in
                    let uu____1769 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1772 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1768.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1768.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1769;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1768.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1772
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1783  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1838 =
                    match uu____1838 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1884 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1900 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1934  ->
                                        fun uu____1935  ->
                                          match (uu____1934, uu____1935) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____2000 =
                                                norm_pat env3 p1 in
                                              (match uu____2000 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1900 with
                               | (pats1,env3) ->
                                   ((let uu___152_2066 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_2066.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_2066.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___153_2080 = x in
                                let uu____2081 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_2080.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_2080.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2081
                                } in
                              ((let uu___154_2087 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_2087.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_2087.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___155_2092 = x in
                                let uu____2093 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_2092.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_2092.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2093
                                } in
                              ((let uu___156_2099 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_2099.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_2099.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___157_2109 = x in
                                let uu____2110 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_2109.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_2109.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2110
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___158_2117 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_2117.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_2117.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2120 = norm_pat env1 pat in
                        (match uu____2120 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2144 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2144 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2149 =
                    let uu____2150 =
                      let uu____2166 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2166) in
                    FStar_Syntax_Syntax.Tm_match uu____2150 in
                  mk uu____2149 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2219 -> closure_as_term cfg env t
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
        | uu____2235 ->
            FStar_List.map
              (fun uu____2245  ->
                 match uu____2245 with
                 | (x,imp) ->
                     let uu____2260 = closure_as_term_delayed cfg env x in
                     (uu____2260, imp)) args
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
        let uu____2272 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2296  ->
                  fun uu____2297  ->
                    match (uu____2296, uu____2297) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___159_2341 = b in
                          let uu____2342 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___159_2341.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___159_2341.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2342
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2272 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2389 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2401 = closure_as_term_delayed cfg env t in
                 let uu____2402 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2401 uu____2402
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2412 = closure_as_term_delayed cfg env t in
                 let uu____2413 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2412 uu____2413
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
                        (fun uu___138_2429  ->
                           match uu___138_2429 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2433 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2433
                           | f -> f)) in
                 let uu____2437 =
                   let uu___160_2438 = c1 in
                   let uu____2439 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2439;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___160_2438.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2437)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___139_2443  ->
            match uu___139_2443 with
            | FStar_Syntax_Syntax.DECREASES uu____2444 -> false
            | uu____2447 -> true))
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
            let uu____2475 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2475
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2492 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2492
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2518 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2542 =
      let uu____2543 =
        let uu____2549 = FStar_Util.string_of_int i in (uu____2549, None) in
      FStar_Const.Const_int uu____2543 in
    const_as_tm uu____2542 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2576 =
    match uu____2576 with
    | (a,uu____2581) ->
        let uu____2583 =
          let uu____2584 = FStar_Syntax_Subst.compress a in
          uu____2584.FStar_Syntax_Syntax.n in
        (match uu____2583 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2594 = FStar_Util.int_of_string i in Some uu____2594
         | uu____2595 -> None) in
  let arg_as_bounded_int uu____2604 =
    match uu____2604 with
    | (a,uu____2611) ->
        let uu____2615 =
          let uu____2616 = FStar_Syntax_Subst.compress a in
          uu____2616.FStar_Syntax_Syntax.n in
        (match uu____2615 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2623;
                FStar_Syntax_Syntax.pos = uu____2624;
                FStar_Syntax_Syntax.vars = uu____2625;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2627;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2628;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2629;_},uu____2630)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2661 =
               let uu____2664 = FStar_Util.int_of_string i in
               (fv1, uu____2664) in
             Some uu____2661
         | uu____2667 -> None) in
  let arg_as_bool uu____2676 =
    match uu____2676 with
    | (a,uu____2681) ->
        let uu____2683 =
          let uu____2684 = FStar_Syntax_Subst.compress a in
          uu____2684.FStar_Syntax_Syntax.n in
        (match uu____2683 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2689 -> None) in
  let arg_as_char uu____2696 =
    match uu____2696 with
    | (a,uu____2701) ->
        let uu____2703 =
          let uu____2704 = FStar_Syntax_Subst.compress a in
          uu____2704.FStar_Syntax_Syntax.n in
        (match uu____2703 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2709 -> None) in
  let arg_as_string uu____2716 =
    match uu____2716 with
    | (a,uu____2721) ->
        let uu____2723 =
          let uu____2724 = FStar_Syntax_Subst.compress a in
          uu____2724.FStar_Syntax_Syntax.n in
        (match uu____2723 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2729)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2732 -> None) in
  let arg_as_list f uu____2753 =
    match uu____2753 with
    | (a,uu____2762) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2781 -> None
          | (Some x)::xs ->
              let uu____2791 = sequence xs in
              (match uu____2791 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2802 = FStar_Syntax_Util.list_elements a in
        (match uu____2802 with
         | None  -> None
         | Some elts ->
             let uu____2812 =
               FStar_List.map
                 (fun x  ->
                    let uu____2817 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2817) elts in
             sequence uu____2812) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2847 = f a in Some uu____2847
    | uu____2848 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2887 = f a0 a1 in Some uu____2887
    | uu____2888 -> None in
  let unary_op as_a f r args =
    let uu____2932 = FStar_List.map as_a args in lift_unary (f r) uu____2932 in
  let binary_op as_a f r args =
    let uu____2982 = FStar_List.map as_a args in lift_binary (f r) uu____2982 in
  let as_primitive_step uu____2999 =
    match uu____2999 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____3037 = f x in int_as_const r uu____3037) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3060 = f x y in int_as_const r uu____3060) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____3077 = f x in bool_as_const r uu____3077) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3100 = f x y in bool_as_const r uu____3100) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3123 = f x y in string_as_const r uu____3123) in
  let list_of_string' rng s =
    let name l =
      let uu____3137 =
        let uu____3138 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3138 in
      mk uu____3137 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3148 =
      let uu____3150 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3150 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3148 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3204 = arg_as_string a1 in
        (match uu____3204 with
         | Some s1 ->
             let uu____3208 = arg_as_list arg_as_string a2 in
             (match uu____3208 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3216 = string_as_const rng r in Some uu____3216
              | uu____3217 -> None)
         | uu____3220 -> None)
    | uu____3222 -> None in
  let string_of_int1 rng i =
    let uu____3233 = FStar_Util.string_of_int i in
    string_as_const rng uu____3233 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3249 = FStar_Util.string_of_int i in
    string_as_const rng uu____3249 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3278)::(a1,uu____3280)::(a2,uu____3282)::[] ->
        let uu____3311 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3311 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____3323 -> None)
    | uu____3324 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____3336 =
      let uu____3346 =
        let uu____3356 =
          let uu____3366 =
            let uu____3376 =
              let uu____3386 =
                let uu____3396 =
                  let uu____3406 =
                    let uu____3416 =
                      let uu____3426 =
                        let uu____3436 =
                          let uu____3446 =
                            let uu____3456 =
                              let uu____3466 =
                                let uu____3476 =
                                  let uu____3486 =
                                    let uu____3496 =
                                      let uu____3506 =
                                        let uu____3516 =
                                          let uu____3526 =
                                            let uu____3535 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____3535,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____3541 =
                                            let uu____3551 =
                                              let uu____3560 =
                                                FStar_Syntax_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____3560,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list arg_as_char)
                                                   string_of_list')) in
                                            let uu____3567 =
                                              let uu____3577 =
                                                let uu____3589 =
                                                  FStar_Syntax_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____3589,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              [uu____3577] in
                                            uu____3551 :: uu____3567 in
                                          uu____3526 :: uu____3541 in
                                        (FStar_Syntax_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____3516 in
                                      (FStar_Syntax_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____3506 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3496 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3486 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3476 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3466 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3456 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3446 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3436 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3426 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3416 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3406 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3396 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3386 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3376 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3366 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3356 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3346 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3336 in
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
      let uu____3939 =
        let uu____3940 =
          let uu____3941 = FStar_Syntax_Syntax.as_arg c in [uu____3941] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3940 in
      uu____3939 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3965 =
              let uu____3974 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3974, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3983  ->
                        fun uu____3984  ->
                          match (uu____3983, uu____3984) with
                          | ((int_to_t1,x),(uu____3995,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____4001 =
              let uu____4011 =
                let uu____4020 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____4020, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____4029  ->
                          fun uu____4030  ->
                            match (uu____4029, uu____4030) with
                            | ((int_to_t1,x),(uu____4041,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____4047 =
                let uu____4057 =
                  let uu____4066 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____4066, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____4075  ->
                            fun uu____4076  ->
                              match (uu____4075, uu____4076) with
                              | ((int_to_t1,x),(uu____4087,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____4057] in
              uu____4011 :: uu____4047 in
            uu____3965 :: uu____4001)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____4153)::(a1,uu____4155)::(a2,uu____4157)::[] ->
        let uu____4186 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4186 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4190 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4190.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4190.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4190.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4197 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4197.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4197.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4197.FStar_Syntax_Syntax.vars)
                })
         | uu____4202 -> None)
    | (_typ,uu____4204)::uu____4205::(a1,uu____4207)::(a2,uu____4209)::[] ->
        let uu____4246 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4246 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4250 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4250.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4250.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4250.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4257 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4257.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4257.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4257.FStar_Syntax_Syntax.vars)
                })
         | uu____4262 -> None)
    | uu____4263 -> failwith "Unexpected number of arguments" in
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
  [propositional_equality; hetero_propositional_equality]
let reduce_primops:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____4275 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4275
      then tm
      else
        (let uu____4277 = FStar_Syntax_Util.head_and_args tm in
         match uu____4277 with
         | (head1,args) ->
             let uu____4303 =
               let uu____4304 = FStar_Syntax_Util.un_uinst head1 in
               uu____4304.FStar_Syntax_Syntax.n in
             (match uu____4303 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4308 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4308 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4323 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4323 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4326 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___163_4335 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4335.tcenv);
           delta_level = (uu___163_4335.delta_level);
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
        let uu___164_4359 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4359.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4359.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4359.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4378 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4406 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4406
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4409;
                     FStar_Syntax_Syntax.pos = uu____4410;
                     FStar_Syntax_Syntax.vars = uu____4411;_},uu____4412);
                FStar_Syntax_Syntax.tk = uu____4413;
                FStar_Syntax_Syntax.pos = uu____4414;
                FStar_Syntax_Syntax.vars = uu____4415;_},args)
             ->
             let uu____4435 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4435
             then
               let uu____4436 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4436 with
                | (Some (true ),uu____4469)::(uu____4470,(arg,uu____4472))::[]
                    -> arg
                | (uu____4513,(arg,uu____4515))::(Some (true ),uu____4516)::[]
                    -> arg
                | (Some (false ),uu____4557)::uu____4558::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4596::(Some (false ),uu____4597)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4635 -> tm1)
             else
               (let uu____4645 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4645
                then
                  let uu____4646 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4646 with
                  | (Some (true ),uu____4679)::uu____4680::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4718::(Some (true ),uu____4719)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4757)::(uu____4758,(arg,uu____4760))::[]
                      -> arg
                  | (uu____4801,(arg,uu____4803))::(Some (false ),uu____4804)::[]
                      -> arg
                  | uu____4845 -> tm1
                else
                  (let uu____4855 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4855
                   then
                     let uu____4856 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4856 with
                     | uu____4889::(Some (true ),uu____4890)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4928)::uu____4929::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4967)::(uu____4968,(arg,uu____4970))::[]
                         -> arg
                     | (uu____5011,(p,uu____5013))::(uu____5014,(q,uu____5016))::[]
                         ->
                         let uu____5058 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5058
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5060 -> tm1
                   else
                     (let uu____5070 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5070
                      then
                        let uu____5071 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5071 with
                        | (Some (true ),uu____5104)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5128)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5152 -> tm1
                      else
                        (let uu____5162 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5162
                         then
                           match args with
                           | (t,uu____5164)::[] ->
                               let uu____5177 =
                                 let uu____5178 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5178.FStar_Syntax_Syntax.n in
                               (match uu____5177 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5181::[],body,uu____5183) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5209 -> tm1)
                                | uu____5211 -> tm1)
                           | (uu____5212,Some (FStar_Syntax_Syntax.Implicit
                              uu____5213))::(t,uu____5215)::[] ->
                               let uu____5242 =
                                 let uu____5243 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5243.FStar_Syntax_Syntax.n in
                               (match uu____5242 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5246::[],body,uu____5248) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5274 -> tm1)
                                | uu____5276 -> tm1)
                           | uu____5277 -> tm1
                         else
                           (let uu____5284 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5284
                            then
                              match args with
                              | (t,uu____5286)::[] ->
                                  let uu____5299 =
                                    let uu____5300 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5300.FStar_Syntax_Syntax.n in
                                  (match uu____5299 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5303::[],body,uu____5305) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5331 -> tm1)
                                   | uu____5333 -> tm1)
                              | (uu____5334,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5335))::
                                  (t,uu____5337)::[] ->
                                  let uu____5364 =
                                    let uu____5365 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5365.FStar_Syntax_Syntax.n in
                                  (match uu____5364 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5368::[],body,uu____5370) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5396 -> tm1)
                                   | uu____5398 -> tm1)
                              | uu____5399 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5407;
                FStar_Syntax_Syntax.pos = uu____5408;
                FStar_Syntax_Syntax.vars = uu____5409;_},args)
             ->
             let uu____5425 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5425
             then
               let uu____5426 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5426 with
                | (Some (true ),uu____5459)::(uu____5460,(arg,uu____5462))::[]
                    -> arg
                | (uu____5503,(arg,uu____5505))::(Some (true ),uu____5506)::[]
                    -> arg
                | (Some (false ),uu____5547)::uu____5548::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5586::(Some (false ),uu____5587)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5625 -> tm1)
             else
               (let uu____5635 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5635
                then
                  let uu____5636 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5636 with
                  | (Some (true ),uu____5669)::uu____5670::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5708::(Some (true ),uu____5709)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5747)::(uu____5748,(arg,uu____5750))::[]
                      -> arg
                  | (uu____5791,(arg,uu____5793))::(Some (false ),uu____5794)::[]
                      -> arg
                  | uu____5835 -> tm1
                else
                  (let uu____5845 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5845
                   then
                     let uu____5846 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5846 with
                     | uu____5879::(Some (true ),uu____5880)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5918)::uu____5919::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5957)::(uu____5958,(arg,uu____5960))::[]
                         -> arg
                     | (uu____6001,(p,uu____6003))::(uu____6004,(q,uu____6006))::[]
                         ->
                         let uu____6048 = FStar_Syntax_Util.term_eq p q in
                         (if uu____6048
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____6050 -> tm1
                   else
                     (let uu____6060 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____6060
                      then
                        let uu____6061 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____6061 with
                        | (Some (true ),uu____6094)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____6118)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____6142 -> tm1
                      else
                        (let uu____6152 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____6152
                         then
                           match args with
                           | (t,uu____6154)::[] ->
                               let uu____6167 =
                                 let uu____6168 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6168.FStar_Syntax_Syntax.n in
                               (match uu____6167 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6171::[],body,uu____6173) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6199 -> tm1)
                                | uu____6201 -> tm1)
                           | (uu____6202,Some (FStar_Syntax_Syntax.Implicit
                              uu____6203))::(t,uu____6205)::[] ->
                               let uu____6232 =
                                 let uu____6233 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6233.FStar_Syntax_Syntax.n in
                               (match uu____6232 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6236::[],body,uu____6238) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6264 -> tm1)
                                | uu____6266 -> tm1)
                           | uu____6267 -> tm1
                         else
                           (let uu____6274 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6274
                            then
                              match args with
                              | (t,uu____6276)::[] ->
                                  let uu____6289 =
                                    let uu____6290 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6290.FStar_Syntax_Syntax.n in
                                  (match uu____6289 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6293::[],body,uu____6295) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6321 -> tm1)
                                   | uu____6323 -> tm1)
                              | (uu____6324,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6325))::
                                  (t,uu____6327)::[] ->
                                  let uu____6354 =
                                    let uu____6355 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6355.FStar_Syntax_Syntax.n in
                                  (match uu____6354 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6358::[],body,uu____6360) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6386 -> tm1)
                                   | uu____6388 -> tm1)
                              | uu____6389 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6396 -> tm1)
let is_norm_request hd1 args =
  let uu____6414 =
    let uu____6418 =
      let uu____6419 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6419.FStar_Syntax_Syntax.n in
    (uu____6418, args) in
  match uu____6414 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6424::uu____6425::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6428::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6430 -> false
let get_norm_request args =
  match args with
  | uu____6452::(tm,uu____6454)::[] -> tm
  | (tm,uu____6464)::[] -> tm
  | uu____6469 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6477  ->
    match uu___140_6477 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6479;
           FStar_Syntax_Syntax.pos = uu____6480;
           FStar_Syntax_Syntax.vars = uu____6481;_},uu____6482,uu____6483))::uu____6484
        -> true
    | uu____6490 -> false
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
            (fun uu____6608  ->
               let uu____6609 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6610 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6611 =
                 let uu____6612 =
                   let uu____6614 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6614 in
                 stack_to_string uu____6612 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6609
                 uu____6610 uu____6611);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6626 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6647 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6656 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6657 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6658;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6659;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6664;
                 FStar_Syntax_Syntax.fv_delta = uu____6665;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6669;
                 FStar_Syntax_Syntax.fv_delta = uu____6670;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6671);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6704 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6704.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6704.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6704.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6730 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6730) && (is_norm_request hd1 args))
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
                 let uu___166_6743 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6743.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6743.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6748;
                  FStar_Syntax_Syntax.pos = uu____6749;
                  FStar_Syntax_Syntax.vars = uu____6750;_},a1::a2::rest)
               ->
               let uu____6784 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6784 with
                | (hd1,uu____6795) ->
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
                    (FStar_Const.Const_reflect uu____6850);
                  FStar_Syntax_Syntax.tk = uu____6851;
                  FStar_Syntax_Syntax.pos = uu____6852;
                  FStar_Syntax_Syntax.vars = uu____6853;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6876 = FStar_List.tl stack1 in
               norm cfg env uu____6876 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6879;
                  FStar_Syntax_Syntax.pos = uu____6880;
                  FStar_Syntax_Syntax.vars = uu____6881;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6904 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6904 with
                | (reify_head,uu____6915) ->
                    let a1 =
                      let uu____6931 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6931 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6934);
                            FStar_Syntax_Syntax.tk = uu____6935;
                            FStar_Syntax_Syntax.pos = uu____6936;
                            FStar_Syntax_Syntax.vars = uu____6937;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6962 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6970 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6970
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6977 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6977
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6980 =
                      let uu____6984 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6984, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6980 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6993  ->
                         match uu___141_6993 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6996 =
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
                 if uu____6996 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____7000 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____7000 in
                  let uu____7001 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____7001 with
                  | None  ->
                      (log cfg
                         (fun uu____7012  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____7018  ->
                            let uu____7019 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____7020 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____7019 uu____7020);
                       (let t3 =
                          let uu____7022 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____7022
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
                          | (UnivArgs (us',uu____7038))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____7051 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____7052 ->
                              let uu____7053 =
                                let uu____7054 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____7054 in
                              failwith uu____7053
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____7061 = lookup_bvar env x in
               (match uu____7061 with
                | Univ uu____7062 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____7077 = FStar_ST.read r in
                      (match uu____7077 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____7096  ->
                                 let uu____7097 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____7098 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____7097
                                   uu____7098);
                            (let uu____7099 =
                               let uu____7100 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____7100.FStar_Syntax_Syntax.n in
                             match uu____7099 with
                             | FStar_Syntax_Syntax.Tm_abs uu____7103 ->
                                 norm cfg env2 stack1 t'
                             | uu____7118 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____7151)::uu____7152 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____7157)::uu____7158 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____7164,uu____7165))::stack_rest ->
                    (match c with
                     | Univ uu____7168 -> norm cfg (c :: env) stack_rest t1
                     | uu____7169 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____7172::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____7185  ->
                                         let uu____7186 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7186);
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
                                           (fun uu___142_7200  ->
                                              match uu___142_7200 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____7201 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7203  ->
                                         let uu____7204 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7204);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____7215  ->
                                         let uu____7216 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7216);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____7217 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7224 ->
                                   let cfg1 =
                                     let uu___167_7232 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_7232.tcenv);
                                       delta_level =
                                         (uu___167_7232.delta_level);
                                       primitive_steps =
                                         (uu___167_7232.primitive_steps)
                                     } in
                                   let uu____7233 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7233)
                          | uu____7234::tl1 ->
                              (log cfg
                                 (fun uu____7244  ->
                                    let uu____7245 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7245);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_7269 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_7269.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7282  ->
                          let uu____7283 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7283);
                     norm cfg env stack2 t1)
                | (Debug uu____7284)::uu____7285 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7287 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7287
                    else
                      (let uu____7289 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7289 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7318 =
                                   let uu____7324 =
                                     let uu____7325 =
                                       let uu____7326 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7326 in
                                     FStar_All.pipe_right uu____7325
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7324
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7318
                                   (fun _0_42  -> Some _0_42)
                             | uu____7351 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7365  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7370  ->
                                 let uu____7371 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7371);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7383 = cfg in
                               let uu____7384 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7383.steps);
                                 tcenv = (uu___169_7383.tcenv);
                                 delta_level = (uu___169_7383.delta_level);
                                 primitive_steps = uu____7384
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7394)::uu____7395 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7399 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7399
                    else
                      (let uu____7401 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7401 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7430 =
                                   let uu____7436 =
                                     let uu____7437 =
                                       let uu____7438 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7438 in
                                     FStar_All.pipe_right uu____7437
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7436
                                     (fun _0_43  -> FStar_Util.Inl _0_43) in
                                 FStar_All.pipe_right uu____7430
                                   (fun _0_44  -> Some _0_44)
                             | uu____7463 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7477  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7482  ->
                                 let uu____7483 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7483);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7495 = cfg in
                               let uu____7496 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7495.steps);
                                 tcenv = (uu___169_7495.tcenv);
                                 delta_level = (uu___169_7495.delta_level);
                                 primitive_steps = uu____7496
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7506)::uu____7507 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7513 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7513
                    else
                      (let uu____7515 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7515 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7544 =
                                   let uu____7550 =
                                     let uu____7551 =
                                       let uu____7552 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7552 in
                                     FStar_All.pipe_right uu____7551
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7550
                                     (fun _0_45  -> FStar_Util.Inl _0_45) in
                                 FStar_All.pipe_right uu____7544
                                   (fun _0_46  -> Some _0_46)
                             | uu____7577 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7591  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7596  ->
                                 let uu____7597 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7597);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7609 = cfg in
                               let uu____7610 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7609.steps);
                                 tcenv = (uu___169_7609.tcenv);
                                 delta_level = (uu___169_7609.delta_level);
                                 primitive_steps = uu____7610
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7620)::uu____7621 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7626 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7626
                    else
                      (let uu____7628 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7628 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7657 =
                                   let uu____7663 =
                                     let uu____7664 =
                                       let uu____7665 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7665 in
                                     FStar_All.pipe_right uu____7664
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7663
                                     (fun _0_47  -> FStar_Util.Inl _0_47) in
                                 FStar_All.pipe_right uu____7657
                                   (fun _0_48  -> Some _0_48)
                             | uu____7690 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7704  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7709  ->
                                 let uu____7710 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7710);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7722 = cfg in
                               let uu____7723 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7722.steps);
                                 tcenv = (uu___169_7722.tcenv);
                                 delta_level = (uu___169_7722.delta_level);
                                 primitive_steps = uu____7723
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7733)::uu____7734 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7744 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7744
                    else
                      (let uu____7746 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7746 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7775 =
                                   let uu____7781 =
                                     let uu____7782 =
                                       let uu____7783 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7783 in
                                     FStar_All.pipe_right uu____7782
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7781
                                     (fun _0_49  -> FStar_Util.Inl _0_49) in
                                 FStar_All.pipe_right uu____7775
                                   (fun _0_50  -> Some _0_50)
                             | uu____7808 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7822  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7827  ->
                                 let uu____7828 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7828);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7840 = cfg in
                               let uu____7841 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7840.steps);
                                 tcenv = (uu___169_7840.tcenv);
                                 delta_level = (uu___169_7840.delta_level);
                                 primitive_steps = uu____7841
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7851 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7851
                    else
                      (let uu____7853 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7853 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7882 =
                                   let uu____7888 =
                                     let uu____7889 =
                                       let uu____7890 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7890 in
                                     FStar_All.pipe_right uu____7889
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7888
                                     (fun _0_51  -> FStar_Util.Inl _0_51) in
                                 FStar_All.pipe_right uu____7882
                                   (fun _0_52  -> Some _0_52)
                             | uu____7915 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7929  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7934  ->
                                 let uu____7935 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7935);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7947 = cfg in
                               let uu____7948 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7947.steps);
                                 tcenv = (uu___169_7947.tcenv);
                                 delta_level = (uu___169_7947.delta_level);
                                 primitive_steps = uu____7948
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
                      (fun uu____7980  ->
                         fun stack2  ->
                           match uu____7980 with
                           | (a,aq) ->
                               let uu____7988 =
                                 let uu____7989 =
                                   let uu____7993 =
                                     let uu____7994 =
                                       let uu____8004 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____8004, false) in
                                     Clos uu____7994 in
                                   (uu____7993, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7989 in
                               uu____7988 :: stack2) args) in
               (log cfg
                  (fun uu____8026  ->
                     let uu____8027 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____8027);
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
                             ((let uu___170_8050 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_8050.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_8050.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____8051 ->
                      let uu____8054 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____8054)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____8057 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____8057 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____8073 =
                          let uu____8074 =
                            let uu____8079 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_8080 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_8080.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_8080.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____8079) in
                          FStar_Syntax_Syntax.Tm_refine uu____8074 in
                        mk uu____8073 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____8093 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____8093
               else
                 (let uu____8095 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____8095 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____8101 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____8107  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____8101 c1 in
                      let t2 =
                        let uu____8114 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____8114 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____8157)::uu____8158 -> norm cfg env stack1 t11
                | (Arg uu____8163)::uu____8164 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____8169;
                       FStar_Syntax_Syntax.pos = uu____8170;
                       FStar_Syntax_Syntax.vars = uu____8171;_},uu____8172,uu____8173))::uu____8174
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____8180)::uu____8181 ->
                    norm cfg env stack1 t11
                | uu____8186 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____8189  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____8202 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____8202
                        | FStar_Util.Inr c ->
                            let uu____8210 = norm_comp cfg env c in
                            FStar_Util.Inr uu____8210 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____8215 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____8215)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____8266,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____8267;
                              FStar_Syntax_Syntax.lbunivs = uu____8268;
                              FStar_Syntax_Syntax.lbtyp = uu____8269;
                              FStar_Syntax_Syntax.lbeff = uu____8270;
                              FStar_Syntax_Syntax.lbdef = uu____8271;_}::uu____8272),uu____8273)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8299 =
                 (let uu____8300 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8300) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8301 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8301))) in
               if uu____8299
               then
                 let env1 =
                   let uu____8304 =
                     let uu____8305 =
                       let uu____8315 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8315,
                         false) in
                     Clos uu____8305 in
                   uu____8304 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8339 =
                    let uu____8342 =
                      let uu____8343 =
                        let uu____8344 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8344
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8343] in
                    FStar_Syntax_Subst.open_term uu____8342 body in
                  match uu____8339 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8350 = lb in
                        let uu____8351 =
                          let uu____8354 =
                            let uu____8355 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8355
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8354
                            (fun _0_53  -> FStar_Util.Inl _0_53) in
                        let uu____8364 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8367 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8351;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8350.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8364;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8350.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8367
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8377  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8393 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8393
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8406 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8428  ->
                        match uu____8428 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8467 =
                                let uu___173_8468 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8468.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8468.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8467 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8406 with
                | (rec_env,memos,uu____8528) ->
                    let uu____8543 =
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
                             let uu____8585 =
                               let uu____8586 =
                                 let uu____8596 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8596, false) in
                               Clos uu____8586 in
                             uu____8585 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8634;
                             FStar_Syntax_Syntax.pos = uu____8635;
                             FStar_Syntax_Syntax.vars = uu____8636;_},uu____8637,uu____8638))::uu____8639
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8645 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8652 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8652
                        then
                          let uu___174_8653 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8653.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8653.primitive_steps)
                          }
                        else
                          (let uu___175_8655 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8655.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8655.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8657 =
                         let uu____8658 = FStar_Syntax_Subst.compress head1 in
                         uu____8658.FStar_Syntax_Syntax.n in
                       match uu____8657 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8672 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8672 with
                            | (uu____8673,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8677 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8684 =
                                         let uu____8685 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8685.FStar_Syntax_Syntax.n in
                                       match uu____8684 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8690,uu____8691))
                                           ->
                                           let uu____8700 =
                                             let uu____8701 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8701.FStar_Syntax_Syntax.n in
                                           (match uu____8700 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8706,msrc,uu____8708))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8717 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8717
                                            | uu____8718 -> None)
                                       | uu____8719 -> None in
                                     let uu____8720 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8720 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8724 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8724.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8724.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8724.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8725 =
                                            FStar_List.tl stack1 in
                                          let uu____8726 =
                                            let uu____8727 =
                                              let uu____8730 =
                                                let uu____8731 =
                                                  let uu____8739 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8739) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8731 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8730 in
                                            uu____8727 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8725 uu____8726
                                      | None  ->
                                          let uu____8756 =
                                            let uu____8757 = is_return body in
                                            match uu____8757 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8760;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8761;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8762;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8767 -> false in
                                          if uu____8756
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
                                               let uu____8787 =
                                                 let uu____8790 =
                                                   let uu____8791 =
                                                     let uu____8806 =
                                                       let uu____8808 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8808] in
                                                     (uu____8806, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8791 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8790 in
                                               uu____8787 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8841 =
                                                 let uu____8842 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8842.FStar_Syntax_Syntax.n in
                                               match uu____8841 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8848::uu____8849::[])
                                                   ->
                                                   let uu____8855 =
                                                     let uu____8858 =
                                                       let uu____8859 =
                                                         let uu____8864 =
                                                           let uu____8866 =
                                                             let uu____8867 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8867 in
                                                           let uu____8868 =
                                                             let uu____8870 =
                                                               let uu____8871
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8871 in
                                                             [uu____8870] in
                                                           uu____8866 ::
                                                             uu____8868 in
                                                         (bind1, uu____8864) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8859 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8858 in
                                                   uu____8855 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8883 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8889 =
                                                 let uu____8892 =
                                                   let uu____8893 =
                                                     let uu____8903 =
                                                       let uu____8905 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8906 =
                                                         let uu____8908 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8909 =
                                                           let uu____8911 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8912 =
                                                             let uu____8914 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8915 =
                                                               let uu____8917
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8918
                                                                 =
                                                                 let uu____8920
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8920] in
                                                               uu____8917 ::
                                                                 uu____8918 in
                                                             uu____8914 ::
                                                               uu____8915 in
                                                           uu____8911 ::
                                                             uu____8912 in
                                                         uu____8908 ::
                                                           uu____8909 in
                                                       uu____8905 ::
                                                         uu____8906 in
                                                     (bind_inst, uu____8903) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8893 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8892 in
                                               uu____8889 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8932 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8932 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8950 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8950 with
                            | (uu____8951,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8974 =
                                        let uu____8975 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8975.FStar_Syntax_Syntax.n in
                                      match uu____8974 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8981) -> t4
                                      | uu____8986 -> head2 in
                                    let uu____8987 =
                                      let uu____8988 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8988.FStar_Syntax_Syntax.n in
                                    match uu____8987 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8993 -> None in
                                  let uu____8994 = maybe_extract_fv head2 in
                                  match uu____8994 with
                                  | Some x when
                                      let uu____9000 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____9000
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____9004 =
                                          maybe_extract_fv head3 in
                                        match uu____9004 with
                                        | Some uu____9007 -> Some true
                                        | uu____9008 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____9011 -> (head2, None) in
                                ((let is_arg_impure uu____9022 =
                                    match uu____9022 with
                                    | (e,q) ->
                                        let uu____9027 =
                                          let uu____9028 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____9028.FStar_Syntax_Syntax.n in
                                        (match uu____9027 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____9043 -> false) in
                                  let uu____9044 =
                                    let uu____9045 =
                                      let uu____9049 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____9049 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____9045 in
                                  if uu____9044
                                  then
                                    let uu____9052 =
                                      let uu____9053 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____9053 in
                                    failwith uu____9052
                                  else ());
                                 (let uu____9055 =
                                    maybe_unfold_action head_app in
                                  match uu____9055 with
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
                                      let uu____9090 = FStar_List.tl stack1 in
                                      norm cfg env uu____9090 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____9104 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____9104 in
                           let uu____9105 = FStar_List.tl stack1 in
                           norm cfg env uu____9105 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____9188  ->
                                     match uu____9188 with
                                     | (pat,wopt,tm) ->
                                         let uu____9226 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9226))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9252 = FStar_List.tl stack1 in
                           norm cfg env uu____9252 tm
                       | uu____9253 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9262;
                             FStar_Syntax_Syntax.pos = uu____9263;
                             FStar_Syntax_Syntax.vars = uu____9264;_},uu____9265,uu____9266))::uu____9267
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9273 -> false in
                    if should_reify
                    then
                      let uu____9274 = FStar_List.tl stack1 in
                      let uu____9275 =
                        let uu____9276 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9276 in
                      norm cfg env uu____9274 uu____9275
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9279 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9279
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_9285 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_9285.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_9285.primitive_steps)
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
                | uu____9287 ->
                    (match stack1 with
                     | uu____9288::uu____9289 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9293)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_alien (b,s) ->
                              norm cfg env
                                ((Meta (m, (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____9310 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9320 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9320
                           | uu____9327 -> m in
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
              let uu____9339 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9339 with
              | (uu____9340,return_repr) ->
                  let return_inst =
                    let uu____9347 =
                      let uu____9348 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9348.FStar_Syntax_Syntax.n in
                    match uu____9347 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9354::[])
                        ->
                        let uu____9360 =
                          let uu____9363 =
                            let uu____9364 =
                              let uu____9369 =
                                let uu____9371 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9371] in
                              (return_tm, uu____9369) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9364 in
                          FStar_Syntax_Syntax.mk uu____9363 in
                        uu____9360 None e.FStar_Syntax_Syntax.pos
                    | uu____9383 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9386 =
                    let uu____9389 =
                      let uu____9390 =
                        let uu____9400 =
                          let uu____9402 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9403 =
                            let uu____9405 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9405] in
                          uu____9402 :: uu____9403 in
                        (return_inst, uu____9400) in
                      FStar_Syntax_Syntax.Tm_app uu____9390 in
                    FStar_Syntax_Syntax.mk uu____9389 in
                  uu____9386 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9418 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9418 with
               | None  ->
                   let uu____9420 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9420
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9421;
                     FStar_TypeChecker_Env.mtarget = uu____9422;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9423;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9434;
                     FStar_TypeChecker_Env.mtarget = uu____9435;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9436;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9454 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9454)
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
                (fun uu____9484  ->
                   match uu____9484 with
                   | (a,imp) ->
                       let uu____9491 = norm cfg env [] a in
                       (uu____9491, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9506 = comp1 in
            let uu____9509 =
              let uu____9510 =
                let uu____9516 = norm cfg env [] t in
                let uu____9517 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9516, uu____9517) in
              FStar_Syntax_Syntax.Total uu____9510 in
            {
              FStar_Syntax_Syntax.n = uu____9509;
              FStar_Syntax_Syntax.tk = (uu___178_9506.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9506.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9506.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9532 = comp1 in
            let uu____9535 =
              let uu____9536 =
                let uu____9542 = norm cfg env [] t in
                let uu____9543 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9542, uu____9543) in
              FStar_Syntax_Syntax.GTotal uu____9536 in
            {
              FStar_Syntax_Syntax.n = uu____9535;
              FStar_Syntax_Syntax.tk = (uu___179_9532.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9532.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9532.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9574  ->
                      match uu____9574 with
                      | (a,i) ->
                          let uu____9581 = norm cfg env [] a in
                          (uu____9581, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9586  ->
                      match uu___143_9586 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9590 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9590
                      | f -> f)) in
            let uu___180_9594 = comp1 in
            let uu____9597 =
              let uu____9598 =
                let uu___181_9599 = ct in
                let uu____9600 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9601 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9604 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9600;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9599.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9601;
                  FStar_Syntax_Syntax.effect_args = uu____9604;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9598 in
            {
              FStar_Syntax_Syntax.n = uu____9597;
              FStar_Syntax_Syntax.tk = (uu___180_9594.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9594.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9594.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9621 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9621.tcenv);
               delta_level = (uu___182_9621.delta_level);
               primitive_steps = (uu___182_9621.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9626 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9626 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9629 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9643 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9643.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9643.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9643.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9653 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9653
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9658 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9658.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9658.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9658.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9658.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9660 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9660.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9660.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9660.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9660.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9661 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9661.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9661.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9661.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9667 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9670  ->
        match uu____9670 with
        | (x,imp) ->
            let uu____9673 =
              let uu___187_9674 = x in
              let uu____9675 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9674.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9674.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9675
              } in
            (uu____9673, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9681 =
          FStar_List.fold_left
            (fun uu____9688  ->
               fun b  ->
                 match uu____9688 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9681 with | (nbs,uu____9705) -> FStar_List.rev nbs
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
            let uu____9722 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9722
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9727 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9727
               then
                 let uu____9731 =
                   let uu____9734 =
                     let uu____9735 =
                       let uu____9738 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9738 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9735 in
                   FStar_Util.Inl uu____9734 in
                 Some uu____9731
               else
                 (let uu____9742 =
                    let uu____9745 =
                      let uu____9746 =
                        let uu____9749 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9749 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9746 in
                    FStar_Util.Inl uu____9745 in
                  Some uu____9742))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9762 -> lopt
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
              ((let uu____9774 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9774
                then
                  let uu____9775 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9776 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9775
                    uu____9776
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9787 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9787.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9807  ->
                    let uu____9808 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9808);
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
              let uu____9845 =
                let uu___189_9846 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9846.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9846.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9846.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9845
          | (Arg (Univ uu____9851,uu____9852,uu____9853))::uu____9854 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9856,uu____9857))::uu____9858 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9870),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9886  ->
                    let uu____9887 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9887);
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
                 (let uu____9898 = FStar_ST.read m in
                  match uu____9898 with
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
                  | Some (uu____9924,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9946 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9946
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9953  ->
                    let uu____9954 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9954);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9959 =
                  log cfg
                    (fun uu____9961  ->
                       let uu____9962 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9963 =
                         let uu____9964 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9971  ->
                                   match uu____9971 with
                                   | (p,uu____9977,uu____9978) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9964
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9962 uu____9963);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9988  ->
                               match uu___144_9988 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9989 -> false)) in
                     let steps' =
                       let uu____9992 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9992
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9995 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9995.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9995.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____10029 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____10045 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____10079  ->
                                   fun uu____10080  ->
                                     match (uu____10079, uu____10080) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____10145 = norm_pat env3 p1 in
                                         (match uu____10145 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____10045 with
                          | (pats1,env3) ->
                              ((let uu___191_10211 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_10211.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_10211.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_10225 = x in
                           let uu____10226 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_10225.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_10225.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10226
                           } in
                         ((let uu___193_10232 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_10232.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_10232.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_10237 = x in
                           let uu____10238 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_10237.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_10237.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10238
                           } in
                         ((let uu___195_10244 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_10244.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_10244.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_10254 = x in
                           let uu____10255 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_10254.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_10254.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10255
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_10262 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_10262.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_10262.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10266 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10269 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10269 with
                                 | (p,wopt,e) ->
                                     let uu____10287 = norm_pat env1 p in
                                     (match uu____10287 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10311 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10311 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10316 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10316) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10326) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10331 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10332;
                        FStar_Syntax_Syntax.fv_delta = uu____10333;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10337;
                        FStar_Syntax_Syntax.fv_delta = uu____10338;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10339);_}
                      -> true
                  | uu____10346 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | None  -> b
                  | Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee_orig p =
                  let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                  let uu____10445 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____10445 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10477 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____10479 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10481 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10493 ->
                                let uu____10494 =
                                  let uu____10495 = is_cons head1 in
                                  Prims.op_Negation uu____10495 in
                                FStar_Util.Inr uu____10494)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10509 =
                             let uu____10510 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10510.FStar_Syntax_Syntax.n in
                           (match uu____10509 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10517 ->
                                let uu____10518 =
                                  let uu____10519 = is_cons head1 in
                                  Prims.op_Negation uu____10519 in
                                FStar_Util.Inr uu____10518))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10553)::rest_a,(p1,uu____10556)::rest_p) ->
                      let uu____10584 = matches_pat t1 p1 in
                      (match uu____10584 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10598 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10669 = matches_pat scrutinee1 p1 in
                      (match uu____10669 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10679  ->
                                 let uu____10680 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10681 =
                                   let uu____10682 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10682
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10680 uu____10681);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10691 =
                                        let uu____10692 =
                                          let uu____10702 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10702, false) in
                                        Clos uu____10692 in
                                      uu____10691 :: env2) env1 s in
                             let uu____10725 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10725))) in
                let uu____10726 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10726
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10742  ->
                match uu___145_10742 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10745 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10749 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps
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
            let uu___198_10773 = config s e in
            {
              steps = (uu___198_10773.steps);
              tcenv = (uu___198_10773.tcenv);
              delta_level = (uu___198_10773.delta_level);
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
      fun t  -> let uu____10798 = config s e in norm_comp uu____10798 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10807 = config [] env in norm_universe uu____10807 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10816 = config [] env in ghost_to_pure_aux uu____10816 [] c
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
        let uu____10830 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10830 in
      let uu____10831 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10831
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10833 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10833.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10833.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10834  ->
                    let uu____10835 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10835))
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
            ((let uu____10850 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10850);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10861 = config [AllowUnboundUniverses] env in
          norm_comp uu____10861 [] c
        with
        | e ->
            ((let uu____10865 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10865);
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
                   let uu____10905 =
                     let uu____10906 =
                       let uu____10911 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10911) in
                     FStar_Syntax_Syntax.Tm_refine uu____10906 in
                   mk uu____10905 t01.FStar_Syntax_Syntax.pos
               | uu____10916 -> t2)
          | uu____10917 -> t2 in
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
        let uu____10946 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10946 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10962 ->
                 let uu____10966 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10966 with
                  | (actuals,uu____10977,uu____10978) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____11004 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____11004 with
                         | (binders,args) ->
                             let uu____11014 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____11017 =
                               let uu____11024 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_54  -> FStar_Util.Inl _0_54) in
                               FStar_All.pipe_right uu____11024
                                 (fun _0_55  -> Some _0_55) in
                             FStar_Syntax_Util.abs binders uu____11014
                               uu____11017)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____11062 =
        let uu____11066 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____11066, (t.FStar_Syntax_Syntax.n)) in
      match uu____11062 with
      | (Some sort,uu____11073) ->
          let uu____11075 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____11075
      | (uu____11076,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____11080 ->
          let uu____11084 = FStar_Syntax_Util.head_and_args t in
          (match uu____11084 with
           | (head1,args) ->
               let uu____11110 =
                 let uu____11111 = FStar_Syntax_Subst.compress head1 in
                 uu____11111.FStar_Syntax_Syntax.n in
               (match uu____11110 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____11114,thead) ->
                    let uu____11128 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____11128 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____11163 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_11167 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_11167.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_11167.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_11167.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_11167.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_11167.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_11167.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_11167.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_11167.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_11167.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_11167.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_11167.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_11167.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_11167.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_11167.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_11167.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_11167.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_11167.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_11167.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_11167.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_11167.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_11167.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_11167.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___204_11167.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___204_11167.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t in
                            match uu____11163 with
                            | (uu____11168,ty,uu____11170) ->
                                eta_expand_with_type env t ty))
                | uu____11171 ->
                    let uu____11172 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_11176 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_11176.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_11176.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_11176.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_11176.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_11176.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_11176.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_11176.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_11176.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_11176.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_11176.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_11176.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_11176.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_11176.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_11176.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_11176.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_11176.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_11176.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_11176.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_11176.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_11176.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_11176.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_11176.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___205_11176.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___205_11176.FStar_TypeChecker_Env.is_native_tactic)
                         }) t in
                    (match uu____11172 with
                     | (uu____11177,ty,uu____11179) ->
                         eta_expand_with_type env t ty)))