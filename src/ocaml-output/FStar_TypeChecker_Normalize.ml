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
let uu___is_Beta : step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____10 -> false 
let uu___is_Iota : step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____14 -> false 
let uu___is_Zeta : step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____18 -> false 
let uu___is_Exclude : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____23 -> false
  
let __proj__Exclude__item___0 : step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let uu___is_WHNF : step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____34 -> false 
let uu___is_Primops : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____38 -> false
  
let uu___is_Eager_unfolding : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____42 -> false
  
let uu___is_Inlining : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____46 -> false
  
let uu___is_NoDeltaSteps : step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____50 -> false
  
let uu___is_UnfoldUntil : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____55 -> false
  
let __proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let uu___is_PureSubtermsWithinComputations : step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____66 -> false
  
let uu___is_Simplify : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____70 -> false
  
let uu___is_EraseUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____74 -> false
  
let uu___is_AllowUnboundUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____78 -> false
  
let uu___is_Reify : step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____82 -> false 
let uu___is_CompressUvars : step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____86 -> false
  
let uu___is_NoFullNorm : step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____90 -> false
  
type steps = step Prims.list
type closure =
  | Clos of (closure Prims.list * FStar_Syntax_Syntax.term * (closure
  Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo *
  Prims.bool) 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let uu___is_Clos : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____120 -> false
  
let __proj__Clos__item___0 :
  closure ->
    (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let uu___is_Univ : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____159 -> false
  
let __proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let uu___is_Dummy : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____170 -> false
  
type env = closure Prims.list
let closure_to_string : closure -> Prims.string =
  fun uu___127_174  ->
    match uu___127_174 with
    | Clos (uu____175,t,uu____177,uu____178) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____189 -> "Univ"
    | Dummy  -> "dummy"
  
type cfg =
  {
  steps: steps ;
  tcenv: FStar_TypeChecker_Env.env ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list }
type branches =
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option *
    FStar_Syntax_Syntax.term) Prims.list
type subst_t = FStar_Syntax_Syntax.subst_elt Prims.list
type stack_elt =
  | Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
  
  | MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo 
  | Match of (env * branches * FStar_Range.range) 
  | Abs of (env * FStar_Syntax_Syntax.binders * env *
  (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
  FStar_Util.either Prims.option * FStar_Range.range) 
  | App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range) 
  | Let of (env * FStar_Syntax_Syntax.binders *
  FStar_Syntax_Syntax.letbinding * FStar_Range.range) 
  | Steps of (steps * FStar_TypeChecker_Env.delta_level Prims.list) 
  | Debug of FStar_Syntax_Syntax.term 
let uu___is_Arg : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____290 -> false
  
let __proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let uu___is_UnivArgs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____314 -> false
  
let __proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let uu___is_MemoLazy : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____338 -> false
  
let __proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let uu___is_Match : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____365 -> false
  
let __proj__Match__item___0 :
  stack_elt -> (env * branches * FStar_Range.range) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let uu___is_Abs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____394 -> false
  
let __proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either Prims.option * FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let uu___is_App : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____433 -> false
  
let __proj__App__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Meta : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____456 -> false
  
let __proj__Meta__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.metadata * FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let uu___is_Let : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____478 -> false
  
let __proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Steps : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____505 -> false
  
let __proj__Steps__item___0 :
  stack_elt -> (steps * FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  -> match projectee with | Steps _0 -> _0 
let uu___is_Debug : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____526 -> false
  
let __proj__Debug__item___0 : stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r 
let set_memo r t =
  let uu____574 = FStar_ST.read r  in
  match uu____574 with
  | Some uu____579 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t) 
let env_to_string : closure Prims.list -> Prims.string =
  fun env  ->
    let uu____588 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____588 (FStar_String.concat "; ")
  
let stack_elt_to_string : stack_elt -> Prims.string =
  fun uu___128_593  ->
    match uu___128_593 with
    | Arg (c,uu____595,uu____596) ->
        let uu____597 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____597
    | MemoLazy uu____598 -> "MemoLazy"
    | Abs (uu____602,bs,uu____604,uu____605,uu____606) ->
        let uu____613 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____613
    | UnivArgs uu____618 -> "UnivArgs"
    | Match uu____622 -> "Match"
    | App (t,uu____627,uu____628) ->
        let uu____629 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____629
    | Meta (m,uu____631) -> "Meta"
    | Let uu____632 -> "Let"
    | Steps (s,uu____638) -> "Steps"
    | Debug t ->
        let uu____642 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____642
  
let stack_to_string : stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____648 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____648 (FStar_String.concat "; ")
  
let log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____662 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____662 then f () else ()
  
let is_empty uu___129_671 =
  match uu___129_671 with | [] -> true | uu____673 -> false 
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____691 ->
      let uu____692 =
        let uu____693 = FStar_Syntax_Print.db_to_string x  in
        FStar_Util.format1 "Failed to find %s\n" uu____693  in
      failwith uu____692
  
let downgrade_ghost_effect_name :
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
  
let norm_universe :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____724 =
            FStar_List.fold_left
              (fun uu____733  ->
                 fun u1  ->
                   match uu____733 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____748 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____748 with
                        | (k_u,n1) ->
                            let uu____757 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____757
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____724 with
          | (uu____767,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____783 = FStar_List.nth env x  in
                 match uu____783 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____786 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____790 ->
                   let uu____791 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____791
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____801 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____801 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____812 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____812 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____817 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____820 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____820 with
                                  | (uu____823,m) -> n1 <= m))
                           in
                        if uu____817 then rest1 else us1
                    | uu____827 -> us1)
               | uu____830 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____833 = aux u3  in
              FStar_List.map (fun _0_32  -> FStar_Syntax_Syntax.U_succ _0_32)
                uu____833
           in
        let uu____835 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____835
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____837 = aux u  in
           match uu____837 with
           | []|(FStar_Syntax_Syntax.U_zero )::[] ->
               FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec closure_as_term :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____934  ->
             let uu____935 = FStar_Syntax_Print.tag_of_term t  in
             let uu____936 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____935
               uu____936);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____937 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____940 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____964 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____974 =
                    let uu____975 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____975  in
                  mk uu____974 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____982 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____982
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____984 = lookup_bvar env x  in
                  (match uu____984 with
                   | Univ uu____985 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____989) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1057 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1057 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____1077 =
                         let uu____1078 =
                           let uu____1093 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____1093)  in
                         FStar_Syntax_Syntax.Tm_abs uu____1078  in
                       mk uu____1077 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1123 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1123 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1154 =
                    let uu____1161 =
                      let uu____1165 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____1165]  in
                    closures_as_binders_delayed cfg env uu____1161  in
                  (match uu____1154 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____1179 =
                         let uu____1180 =
                           let uu____1185 =
                             let uu____1186 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____1186 Prims.fst  in
                           (uu____1185, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____1180  in
                       mk uu____1179 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,FStar_Util.Inl t2,lopt)
                  ->
                  let uu____1216 =
                    let uu____1217 =
                      let uu____1230 = closure_as_term_delayed cfg env t11
                         in
                      let uu____1233 =
                        let uu____1240 = closure_as_term_delayed cfg env t2
                           in
                        FStar_All.pipe_left
                          (fun _0_33  -> FStar_Util.Inl _0_33) uu____1240
                         in
                      (uu____1230, uu____1233, lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1217  in
                  mk uu____1216 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_ascribed (t11,FStar_Util.Inr c,lopt)
                  ->
                  let uu____1285 =
                    let uu____1286 =
                      let uu____1299 = closure_as_term_delayed cfg env t11
                         in
                      let uu____1302 =
                        let uu____1309 = close_comp cfg env c  in
                        FStar_All.pipe_left
                          (fun _0_34  -> FStar_Util.Inr _0_34) uu____1309
                         in
                      (uu____1299, uu____1302, lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1286  in
                  mk uu____1285 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1345 =
                    let uu____1346 =
                      let uu____1351 = closure_as_term_delayed cfg env t'  in
                      let uu____1354 =
                        let uu____1355 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____1355  in
                      (uu____1351, uu____1354)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1346  in
                  mk uu____1345 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1397 =
                    let uu____1398 =
                      let uu____1403 = closure_as_term_delayed cfg env t'  in
                      let uu____1406 =
                        let uu____1407 =
                          let uu____1412 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____1412)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____1407  in
                      (uu____1403, uu____1406)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1398  in
                  mk uu____1397 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1431 =
                    let uu____1432 =
                      let uu____1437 = closure_as_term_delayed cfg env t'  in
                      let uu____1440 =
                        let uu____1441 =
                          let uu____1447 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____1447)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1441  in
                      (uu____1437, uu____1440)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1432  in
                  mk uu____1431 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1460 =
                    let uu____1461 =
                      let uu____1466 = closure_as_term_delayed cfg env t'  in
                      (uu____1466, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1461  in
                  mk uu____1460 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1487  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1498 -> body
                    | FStar_Util.Inl uu____1499 ->
                        closure_as_term cfg (Dummy :: env0) body
                     in
                  let lb1 =
                    let uu___141_1501 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___141_1501.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___141_1501.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___141_1501.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    }  in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1508,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1532  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____1537 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____1537
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1541  -> fun env2  -> Dummy :: env2) lbs
                          env_univs
                       in
                    let uu___142_1544 = lb  in
                    let uu____1545 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let uu____1548 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___142_1544.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___142_1544.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1545;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___142_1544.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1548
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1559  -> fun env1  -> Dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____1614 =
                    match uu____1614 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1660 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                              let uu____1680 = norm_pat env2 hd1  in
                              (match uu____1680 with
                               | (hd2,env') ->
                                   let tl2 =
                                     FStar_All.pipe_right tl1
                                       (FStar_List.map
                                          (fun p1  ->
                                             let uu____1716 =
                                               norm_pat env2 p1  in
                                             Prims.fst uu____1716))
                                      in
                                   ((let uu___143_1728 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___143_1728.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___143_1728.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1745 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1779  ->
                                        fun uu____1780  ->
                                          match (uu____1779, uu____1780) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1845 =
                                                norm_pat env3 p1  in
                                              (match uu____1845 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____1745 with
                               | (pats1,env3) ->
                                   ((let uu___144_1911 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___144_1911.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___144_1911.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___145_1925 = x  in
                                let uu____1926 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___145_1925.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___145_1925.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1926
                                }  in
                              ((let uu___146_1932 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___146_1932.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___146_1932.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___147_1937 = x  in
                                let uu____1938 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___147_1937.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___147_1937.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1938
                                }  in
                              ((let uu___148_1944 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___148_1944.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___148_1944.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___149_1954 = x  in
                                let uu____1955 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___149_1954.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___149_1954.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1955
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___150_1962 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___150_1962.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___150_1962.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____1965 = norm_pat env1 pat  in
                        (match uu____1965 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1989 =
                                     closure_as_term cfg env2 w  in
                                   Some uu____1989
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____1994 =
                    let uu____1995 =
                      let uu____2011 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____2011)  in
                    FStar_Syntax_Syntax.Tm_match uu____1995  in
                  mk uu____1994 t1.FStar_Syntax_Syntax.pos))

and closure_as_term_delayed :
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
        | uu____2064 -> closure_as_term cfg env t

and closures_as_args_delayed :
  cfg ->
    closure Prims.list ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list ->
        ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____2080 ->
            FStar_List.map
              (fun uu____2090  ->
                 match uu____2090 with
                 | (x,imp) ->
                     let uu____2105 = closure_as_term_delayed cfg env x  in
                     (uu____2105, imp)) args

and closures_as_binders_delayed :
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
          closure Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____2117 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2141  ->
                  fun uu____2142  ->
                    match (uu____2141, uu____2142) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___151_2186 = b  in
                          let uu____2187 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___151_2186.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___151_2186.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2187
                          }  in
                        let env2 = Dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____2117 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and close_comp :
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
        | uu____2234 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2246 = closure_as_term_delayed cfg env t  in
                 let uu____2247 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____2246 uu____2247
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2257 = closure_as_term_delayed cfg env t  in
                 let uu____2258 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2257 uu____2258
             | FStar_Syntax_Syntax.Comp c1 ->
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___130_2271  ->
                           match uu___130_2271 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2275 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____2275
                           | f -> f))
                    in
                 let uu____2279 =
                   let uu___152_2280 = c1  in
                   let uu____2281 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_typ_name =
                       (uu___152_2280.FStar_Syntax_Syntax.comp_typ_name);
                     FStar_Syntax_Syntax.comp_univs = uu____2281;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____2279)

and filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
      (FStar_List.filter
         (fun uu___131_2285  ->
            match uu___131_2285 with
            | FStar_Syntax_Syntax.DECREASES uu____2286 -> false
            | uu____2289 -> true))

and close_lcomp_opt :
  cfg ->
    closure Prims.list ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either Prims.option ->
        (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                     FStar_Syntax_Syntax.cflags Prims.list))
          FStar_Util.either Prims.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some (FStar_Util.Inl lc) ->
            let flags = filter_out_lcomp_cflags lc  in
            let uu____2317 = FStar_Syntax_Util.is_total_lcomp lc  in
            if uu____2317
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2334 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
               if uu____2334
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr
                      ((lc.FStar_Syntax_Syntax.lcomp_name), flags)))
        | uu____2360 -> lopt

let arith_ops :
  (FStar_Ident.lident * (Prims.int -> Prims.int -> FStar_Const.sconst))
    Prims.list
  =
  let int_as_const i =
    let uu____2378 =
      let uu____2384 = FStar_Util.string_of_int i  in (uu____2384, None)  in
    FStar_Const.Const_int uu____2378  in
  let bool_as_const b = FStar_Const.Const_bool b  in
  let uu____2394 =
    let uu____2402 =
      FStar_List.map
        (fun m  ->
           let uu____2419 =
             let uu____2426 = FStar_Syntax_Const.p2l ["FStar"; m; "add"]  in
             (uu____2426, (fun x  -> fun y  -> int_as_const (x + y)))  in
           let uu____2433 =
             let uu____2441 =
               let uu____2448 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"]
                  in
               (uu____2448, (fun x  -> fun y  -> int_as_const (x - y)))  in
             let uu____2455 =
               let uu____2463 =
                 let uu____2470 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"]
                    in
                 (uu____2470, (fun x  -> fun y  -> int_as_const (x * y)))  in
               [uu____2463]  in
             uu____2441 :: uu____2455  in
           uu____2419 :: uu____2433)
        ["Int8";
        "UInt8";
        "Int16";
        "UInt16";
        "Int32";
        "UInt32";
        "Int64";
        "UInt64";
        "UInt128"]
       in
    FStar_List.flatten uu____2402  in
  FStar_List.append
    [(FStar_Syntax_Const.op_Addition,
       ((fun x  -> fun y  -> int_as_const (x + y))));
    (FStar_Syntax_Const.op_Subtraction,
      ((fun x  -> fun y  -> int_as_const (x - y))));
    (FStar_Syntax_Const.op_Multiply,
      ((fun x  -> fun y  -> int_as_const (x * y))));
    (FStar_Syntax_Const.op_Division,
      ((fun x  -> fun y  -> int_as_const (x / y))));
    (FStar_Syntax_Const.op_LT, ((fun x  -> fun y  -> bool_as_const (x < y))));
    (FStar_Syntax_Const.op_LTE,
      ((fun x  -> fun y  -> bool_as_const (x <= y))));
    (FStar_Syntax_Const.op_GT, ((fun x  -> fun y  -> bool_as_const (x > y))));
    (FStar_Syntax_Const.op_GTE,
      ((fun x  -> fun y  -> bool_as_const (x >= y))));
    (FStar_Syntax_Const.op_Modulus,
      ((fun x  -> fun y  -> int_as_const (x mod y))))] uu____2394
  
let un_ops :
  (FStar_Ident.lident *
    (Prims.string ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax))
    Prims.list
  =
  let mk1 x = mk x FStar_Range.dummyRange  in
  let name x =
    let uu____2665 =
      let uu____2666 =
        let uu____2667 = FStar_Syntax_Const.p2l x  in
        FStar_Syntax_Syntax.lid_as_fv uu____2667
          FStar_Syntax_Syntax.Delta_constant None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____2666  in
    mk1 uu____2665  in
  let ctor x =
    let uu____2676 =
      let uu____2677 =
        let uu____2678 = FStar_Syntax_Const.p2l x  in
        FStar_Syntax_Syntax.lid_as_fv uu____2678
          FStar_Syntax_Syntax.Delta_constant
          (Some FStar_Syntax_Syntax.Data_ctor)
         in
      FStar_Syntax_Syntax.Tm_fvar uu____2677  in
    mk1 uu____2676  in
  let uu____2679 =
    let uu____2686 =
      FStar_Syntax_Const.p2l ["FStar"; "String"; "list_of_string"]  in
    (uu____2686,
      (fun s  ->
         let uu____2692 = FStar_String.list_of_string s  in
         let uu____2694 =
           let uu____2697 =
             let uu____2698 =
               let uu____2708 =
                 let uu____2709 = ctor ["Prims"; "Nil"]  in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2709
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let uu____2710 =
                 let uu____2717 =
                   let uu____2723 = name ["FStar"; "Char"; "char"]  in
                   (uu____2723, (Some (FStar_Syntax_Syntax.Implicit true)))
                    in
                 [uu____2717]  in
               (uu____2708, uu____2710)  in
             FStar_Syntax_Syntax.Tm_app uu____2698  in
           mk1 uu____2697  in
         FStar_List.fold_right
           (fun c  ->
              fun a  ->
                let uu____2751 =
                  let uu____2752 =
                    let uu____2762 =
                      let uu____2763 = ctor ["Prims"; "Cons"]  in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____2763
                        [FStar_Syntax_Syntax.U_zero]
                       in
                    let uu____2764 =
                      let uu____2771 =
                        let uu____2777 = name ["FStar"; "Char"; "char"]  in
                        (uu____2777,
                          (Some (FStar_Syntax_Syntax.Implicit true)))
                         in
                      let uu____2783 =
                        let uu____2790 =
                          let uu____2796 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_char c))
                             in
                          (uu____2796, None)  in
                        [uu____2790; (a, None)]  in
                      uu____2771 :: uu____2783  in
                    (uu____2762, uu____2764)  in
                  FStar_Syntax_Syntax.Tm_app uu____2752  in
                mk1 uu____2751) uu____2692 uu____2694))
     in
  [uu____2679] 
let reduce_equality :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let is_decidable_equality t =
      let uu____2856 =
        let uu____2857 = FStar_Syntax_Util.un_uinst t  in
        uu____2857.FStar_Syntax_Syntax.n  in
      match uu____2856 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq
      | uu____2861 -> false  in
    let is_propositional_equality t =
      let uu____2866 =
        let uu____2867 = FStar_Syntax_Util.un_uinst t  in
        uu____2867.FStar_Syntax_Syntax.n  in
      match uu____2866 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
      | uu____2871 -> false  in
    match tm.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app
        (op_eq_inst,(_typ,uu____2876)::(a1,uu____2878)::(a2,uu____2880)::[])
        when is_decidable_equality op_eq_inst ->
        let tt =
          let uu____2921 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2921 with
          | FStar_Syntax_Util.Equal  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool true)) tm.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Util.NotEqual  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool false)) tm.FStar_Syntax_Syntax.pos
          | uu____2924 -> tm  in
        tt
    | FStar_Syntax_Syntax.Tm_app (eq2_inst,_::(a1,_)::(a2,_)::[])
      |FStar_Syntax_Syntax.Tm_app (eq2_inst,(a1,_)::(a2,_)::[]) when
        is_propositional_equality eq2_inst ->
        let tt =
          let uu____2996 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2996 with
          | FStar_Syntax_Util.Equal  -> FStar_Syntax_Util.t_true
          | FStar_Syntax_Util.NotEqual  -> FStar_Syntax_Util.t_false
          | uu____2997 -> tm  in
        tt
    | uu____2998 -> tm
  
let find_fv fv ops =
  match fv.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv1 ->
      FStar_List.tryFind
        (fun uu____3023  ->
           match uu____3023 with
           | (l,uu____3027) -> FStar_Syntax_Syntax.fv_eq_lid fv1 l) ops
  | uu____3028 -> None 
let reduce_primops :
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let uu____3045 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops steps)
         in
      if uu____3045
      then tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             (fv,(a1,uu____3053)::(a2,uu____3055)::[]) ->
             let uu____3085 = find_fv fv arith_ops  in
             (match uu____3085 with
              | None  -> tm
              | Some (uu____3105,op) ->
                  let norm i j =
                    let c =
                      let uu____3131 = FStar_Util.int_of_string i  in
                      let uu____3132 = FStar_Util.int_of_string j  in
                      op uu____3131 uu____3132  in
                    mk (FStar_Syntax_Syntax.Tm_constant c)
                      tm.FStar_Syntax_Syntax.pos
                     in
                  let uu____3133 =
                    let uu____3136 =
                      let uu____3137 = FStar_Syntax_Subst.compress a1  in
                      uu____3137.FStar_Syntax_Syntax.n  in
                    let uu____3140 =
                      let uu____3141 = FStar_Syntax_Subst.compress a2  in
                      uu____3141.FStar_Syntax_Syntax.n  in
                    (uu____3136, uu____3140)  in
                  (match uu____3133 with
                   | (FStar_Syntax_Syntax.Tm_app
                      (head1,(arg1,uu____3148)::[]),FStar_Syntax_Syntax.Tm_app
                      (head2,(arg2,uu____3151)::[])) ->
                       let uu____3194 =
                         let uu____3199 =
                           let uu____3200 = FStar_Syntax_Subst.compress head1
                              in
                           uu____3200.FStar_Syntax_Syntax.n  in
                         let uu____3203 =
                           let uu____3204 = FStar_Syntax_Subst.compress head2
                              in
                           uu____3204.FStar_Syntax_Syntax.n  in
                         let uu____3207 =
                           let uu____3208 = FStar_Syntax_Subst.compress arg1
                              in
                           uu____3208.FStar_Syntax_Syntax.n  in
                         let uu____3211 =
                           let uu____3212 = FStar_Syntax_Subst.compress arg2
                              in
                           uu____3212.FStar_Syntax_Syntax.n  in
                         (uu____3199, uu____3203, uu____3207, uu____3211)  in
                       (match uu____3194 with
                        | (FStar_Syntax_Syntax.Tm_fvar
                           fv1,FStar_Syntax_Syntax.Tm_fvar
                           fv2,FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int
                           (i,None )),FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (j,None ))) when
                            (FStar_Util.ends_with
                               (FStar_Ident.text_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               "int_to_t")
                              &&
                              (FStar_Util.ends_with
                                 (FStar_Ident.text_of_lid
                                    (fv2.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                 "int_to_t")
                            ->
                            let uu____3239 =
                              mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                                tm.FStar_Syntax_Syntax.pos
                               in
                            let uu____3242 =
                              let uu____3248 =
                                let uu____3254 = norm i j  in
                                (uu____3254, None)  in
                              [uu____3248]  in
                            FStar_Syntax_Util.mk_app uu____3239 uu____3242
                        | uu____3270 -> tm)
                   | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                      (i,None )),FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (j,None ))) -> norm i j
                   | uu____3287 -> tm))
         | FStar_Syntax_Syntax.Tm_app (fv,(a1,uu____3292)::[]) ->
             let uu____3314 = find_fv fv un_ops  in
             (match uu____3314 with
              | None  -> tm
              | Some (uu____3334,op) ->
                  let uu____3350 =
                    let uu____3351 = FStar_Syntax_Subst.compress a1  in
                    uu____3351.FStar_Syntax_Syntax.n  in
                  (match uu____3350 with
                   | FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_string (b,uu____3357)) ->
                       let uu____3360 = FStar_Bytes.unicode_bytes_as_string b
                          in
                       op uu____3360
                   | uu____3361 -> tm))
         | uu____3362 -> reduce_equality tm)
  
let maybe_simplify :
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let w t =
        let uu___153_3387 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___153_3387.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___153_3387.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___153_3387.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____3406 -> None  in
      let simplify arg = ((simp_t (Prims.fst arg)), arg)  in
      let uu____3433 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps)
         in
      if uu____3433
      then reduce_primops steps tm
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
             let uu____3477 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid
                in
             if uu____3477
             then
               let uu____3480 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               (match uu____3480 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____3648 -> tm)
             else
               (let uu____3658 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid
                   in
                if uu____3658
                then
                  let uu____3661 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____3661 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____3829 -> tm
                else
                  (let uu____3839 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid
                      in
                   if uu____3839
                   then
                     let uu____3842 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____3842 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____3933)::(uu____3934,(arg,uu____3936))::[]
                         -> arg
                     | uu____3977 -> tm
                   else
                     (let uu____3987 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid
                         in
                      if uu____3987
                      then
                        let uu____3990 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____3990 with
                        | (Some (true ),uu____4025)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4049)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4073 -> tm
                      else
                        (let uu____4083 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid)
                            in
                         if uu____4083
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____4128 =
                                 let uu____4129 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____4129.FStar_Syntax_Syntax.n  in
                               (match uu____4128 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4134::[],body,uu____4136) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____4164 -> tm)
                                | uu____4166 -> tm)
                           | uu____4167 -> tm
                         else reduce_equality tm))))
         | uu____4174 -> tm)
  
let is_norm_request hd1 args =
  let uu____4189 =
    let uu____4193 =
      let uu____4194 = FStar_Syntax_Util.un_uinst hd1  in
      uu____4194.FStar_Syntax_Syntax.n  in
    (uu____4193, args)  in
  match uu____4189 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4199::uu____4200::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4203::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4205 -> false 
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____4238 -> failwith "Impossible" 
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____4334  ->
               let uu____4335 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____4336 = FStar_Syntax_Print.term_to_string t1  in
               let uu____4337 = stack_to_string stack1  in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4335
                 uu____4336 uu____4337);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4338 ->
               failwith "Impossible"
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
               ((let uu____4385 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____4385) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Syntax_Const.prims_lid))
               ->
               let tm = get_norm_request args  in
               let s =
                 [Reify;
                 Beta;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 Zeta;
                 Iota;
                 Primops]  in
               let cfg' =
                 let uu___154_4398 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___154_4398.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant]
                 }  in
               let stack' = (Debug t1) ::
                 (Steps ((cfg.steps), (cfg.delta_level))) :: stack1  in
               norm cfg' env stack' tm
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4402;
                  FStar_Syntax_Syntax.pos = uu____4403;
                  FStar_Syntax_Syntax.vars = uu____4404;_},a1::a2::rest)
               ->
               let uu____4438 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____4438 with
                | (hd1,uu____4449) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd1, [a1])) None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let t2 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest))) None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    norm cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4504;
                  FStar_Syntax_Syntax.pos = uu____4505;
                  FStar_Syntax_Syntax.vars = uu____4506;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4529 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____4529 with
                | (reify_head,uu____4540) ->
                    let a1 =
                      let uu____4556 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a)
                         in
                      FStar_Syntax_Subst.compress uu____4556  in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____4559);
                            FStar_Syntax_Syntax.tk = uu____4560;
                            FStar_Syntax_Syntax.pos = uu____4561;
                            FStar_Syntax_Syntax.vars = uu____4562;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____4587 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1  in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____4595 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack1 uu____4595
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____4602 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____4602
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____4605 =
                      let uu____4609 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____4609, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____4605  in
                  let stack2 = us1 :: stack1  in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1  in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___132_4618  ->
                         match uu___132_4618 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l))
                  in
               if Prims.op_Negation should_delta
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____4622 = FStar_Syntax_Syntax.range_of_fv f  in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____4622  in
                  let uu____4623 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  match uu____4623 with
                  | None  ->
                      (log cfg
                         (fun uu____4634  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____4640  ->
                            let uu____4641 =
                              FStar_Syntax_Print.term_to_string t0  in
                            let uu____4642 =
                              FStar_Syntax_Print.term_to_string t2  in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____4641 uu____4642);
                       (let n1 = FStar_List.length us  in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____4649))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env)
                                 in
                              norm cfg env1 stack2 t2
                          | uu____4662 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t2
                          | uu____4663 ->
                              let uu____4664 =
                                let uu____4665 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____4665
                                 in
                              failwith uu____4664
                        else norm cfg env stack1 t2)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____4672 = lookup_bvar env x  in
               (match uu____4672 with
                | Univ uu____4673 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____4688 = FStar_ST.read r  in
                      (match uu____4688 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____4707  ->
                                 let uu____4708 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____4709 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____4708
                                   uu____4709);
                            (let uu____4710 =
                               let uu____4711 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____4711.FStar_Syntax_Syntax.n  in
                             match uu____4710 with
                             | FStar_Syntax_Syntax.Tm_abs uu____4714 ->
                                 norm cfg env2 stack1 t'
                             | uu____4729 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____4762)::uu____4763 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4768)::uu____4769 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4775,uu____4776))::stack_rest ->
                    (match c with
                     | Univ uu____4779 -> norm cfg (c :: env) stack_rest t1
                     | uu____4780 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____4783::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____4796  ->
                                         let uu____4797 = closure_to_string c
                                            in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4797);
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
                                           (fun uu___133_4811  ->
                                              match uu___133_4811 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____4812 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____4814  ->
                                         let uu____4815 = closure_to_string c
                                            in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4815);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____4826  ->
                                         let uu____4827 = closure_to_string c
                                            in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4827);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____4828 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____4835 ->
                                   let cfg1 =
                                     let uu___155_4843 = cfg  in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___155_4843.tcenv);
                                       delta_level =
                                         (uu___155_4843.delta_level)
                                     }  in
                                   let uu____4844 =
                                     closure_as_term cfg1 env t1  in
                                   rebuild cfg1 env stack1 uu____4844)
                          | uu____4845::tl1 ->
                              (log cfg
                                 (fun uu____4855  ->
                                    let uu____4856 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____4856);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,dl))::stack2 ->
                    norm
                      (let uu___156_4877 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___156_4877.tcenv);
                         delta_level = dl
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____4890  ->
                          let uu____4891 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____4891);
                     norm cfg env stack2 t1)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____4902 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____4902
                    else
                      (let uu____4904 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____4904 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____4933 =
                                   let uu____4939 =
                                     let uu____4940 =
                                       let uu____4941 =
                                         l.FStar_Syntax_Syntax.lcomp_as_comp
                                           ()
                                          in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____4941
                                        in
                                     FStar_TypeChecker_Env.lcomp_of_comp
                                       cfg.tcenv uu____4940
                                      in
                                   FStar_Util.Inl uu____4939  in
                                 Some uu____4933
                             | uu____4950 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____4964  -> Dummy :: env1) env)
                              in
                           (log cfg
                              (fun uu____4969  ->
                                 let uu____4970 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____4970);
                            norm cfg env'
                              ((Abs
                                  (env, bs1, env', lopt1,
                                    (t1.FStar_Syntax_Syntax.pos))) :: stack1)
                              body1)))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____5004  ->
                         fun stack2  ->
                           match uu____5004 with
                           | (a,aq) ->
                               let uu____5012 =
                                 let uu____5013 =
                                   let uu____5017 =
                                     let uu____5018 =
                                       let uu____5028 =
                                         FStar_Util.mk_ref None  in
                                       (env, a, uu____5028, false)  in
                                     Clos uu____5018  in
                                   (uu____5017, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____5013  in
                               uu____5012 :: stack2) args)
                  in
               (log cfg
                  (fun uu____5050  ->
                     let uu____5051 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5051);
                norm cfg env stack2 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 (match (env, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___157_5072 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_5072.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_5072.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack1 t2
                  | uu____5073 ->
                      let uu____5076 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____5076)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____5079 = FStar_Syntax_Subst.open_term [(x, None)] f
                     in
                  match uu____5079 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1  in
                      let t2 =
                        let uu____5095 =
                          let uu____5096 =
                            let uu____5101 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_5102 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_5102.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_5102.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____5101)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____5096  in
                        mk uu____5095 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____5115 = closure_as_term cfg env t1  in
                 rebuild cfg env stack1 uu____5115
               else
                 (let uu____5117 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____5117 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____5123 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____5129  -> Dummy :: env1)
                               env)
                           in
                        norm_comp cfg uu____5123 c1  in
                      let t2 =
                        let uu____5134 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____5134 c2  in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,tc,l) ->
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
                | uu____5170 ->
                    let t12 = norm cfg env [] t11  in
                    (log cfg
                       (fun uu____5173  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____5186 = norm cfg env [] t2  in
                            FStar_Util.Inl uu____5186
                        | FStar_Util.Inr c ->
                            let uu____5194 = norm_comp cfg env c  in
                            FStar_Util.Inr uu____5194
                         in
                      let uu____5195 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t12, tc1, l))
                          t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack1 uu____5195)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1  in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5240,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5241;
                              FStar_Syntax_Syntax.lbunivs = uu____5242;
                              FStar_Syntax_Syntax.lbtyp = uu____5243;
                              FStar_Syntax_Syntax.lbeff = uu____5244;
                              FStar_Syntax_Syntax.lbdef = uu____5245;_}::uu____5246),uu____5247)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____5273 =
                 (let uu____5274 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____5274) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____5275 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)
                             in
                          Prims.op_Negation uu____5275)))
                  in
               if uu____5273
               then
                 let env1 =
                   let uu____5278 =
                     let uu____5279 =
                       let uu____5289 = FStar_Util.mk_ref None  in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____5289,
                         false)
                        in
                     Clos uu____5279  in
                   uu____5278 :: env  in
                 norm cfg env1 stack1 body
               else
                 (let uu____5313 =
                    let uu____5316 =
                      let uu____5317 =
                        let uu____5318 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left
                           in
                        FStar_All.pipe_right uu____5318
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [uu____5317]  in
                    FStar_Syntax_Subst.open_term uu____5316 body  in
                  match uu____5313 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___159_5324 = lb  in
                        let uu____5325 =
                          let uu____5328 =
                            let uu____5329 = FStar_List.hd bs  in
                            FStar_All.pipe_right uu____5329 Prims.fst  in
                          FStar_All.pipe_right uu____5328
                            (fun _0_35  -> FStar_Util.Inl _0_35)
                           in
                        let uu____5338 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                        let uu____5341 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____5325;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___159_5324.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5338;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___159_5324.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5341
                        }  in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____5351  -> Dummy :: env1)
                             env)
                         in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____5367 = closure_as_term cfg env t1  in
               rebuild cfg env stack1 uu____5367
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____5380 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____5402  ->
                        match uu____5402 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____5441 =
                                let uu___160_5442 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_5442.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___160_5442.FStar_Syntax_Syntax.sort)
                                }  in
                              FStar_Syntax_Syntax.bv_to_tm uu____5441  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo = FStar_Util.mk_ref None  in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____5380 with
                | (rec_env,memos,uu____5502) ->
                    let uu____5517 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.write memo
                               (Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (Prims.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____5559 =
                               let uu____5560 =
                                 let uu____5570 = FStar_Util.mk_ref None  in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____5570, false)
                                  in
                               Clos uu____5560  in
                             uu____5559 :: env1) (Prims.snd lbs) env
                       in
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
                             FStar_Syntax_Syntax.tk = uu____5608;
                             FStar_Syntax_Syntax.pos = uu____5609;
                             FStar_Syntax_Syntax.vars = uu____5610;_},uu____5611,uu____5612))::uu____5613
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5619 -> false  in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2  in
                      let stack2 = (Steps ((cfg.steps), (cfg.delta_level)))
                        :: stack1  in
                      let cfg1 =
                        let uu___161_5625 = cfg  in
                        {
                          steps =
                            (FStar_List.append [NoDeltaSteps; Exclude Zeta]
                               cfg.steps);
                          tcenv = (uu___161_5625.tcenv);
                          delta_level = [FStar_TypeChecker_Env.NoDelta]
                        }  in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____5627 =
                         let uu____5628 = FStar_Syntax_Subst.compress head1
                            in
                         uu____5628.FStar_Syntax_Syntax.n  in
                       match uu____5627 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____5642 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____5642 with
                            | (uu____5643,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inl x ->
                                     let head2 =
                                       FStar_All.pipe_left
                                         FStar_Syntax_Util.mk_reify
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     let body1 =
                                       FStar_All.pipe_left
                                         FStar_Syntax_Util.mk_reify body
                                        in
                                     let body2 =
                                       let uu____5665 =
                                         let uu____5668 =
                                           let uu____5669 =
                                             let uu____5684 =
                                               let uu____5686 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x
                                                  in
                                               [uu____5686]  in
                                             (uu____5684, body1, None)  in
                                           FStar_Syntax_Syntax.Tm_abs
                                             uu____5669
                                            in
                                         FStar_Syntax_Syntax.mk uu____5668
                                          in
                                       uu____5665 None
                                         body1.FStar_Syntax_Syntax.pos
                                        in
                                     let bind_inst =
                                       let uu____5712 =
                                         let uu____5713 =
                                           FStar_Syntax_Subst.compress
                                             bind_repr
                                            in
                                         uu____5713.FStar_Syntax_Syntax.n  in
                                       match uu____5712 with
                                       | FStar_Syntax_Syntax.Tm_uinst
                                           (bind1,uu____5719::uu____5720::[])
                                           ->
                                           let uu____5726 =
                                             let uu____5729 =
                                               let uu____5730 =
                                                 let uu____5735 =
                                                   let uu____5737 =
                                                     (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                       cfg.tcenv
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____5738 =
                                                     let uu____5740 =
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv t2
                                                        in
                                                     [uu____5740]  in
                                                   uu____5737 :: uu____5738
                                                    in
                                                 (bind1, uu____5735)  in
                                               FStar_Syntax_Syntax.Tm_uinst
                                                 uu____5730
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____5729
                                              in
                                           uu____5726 None
                                             t2.FStar_Syntax_Syntax.pos
                                       | uu____5752 ->
                                           failwith
                                             "NIY : Reification of indexed effects"
                                        in
                                     let reified =
                                       let uu____5758 =
                                         let uu____5761 =
                                           let uu____5762 =
                                             let uu____5772 =
                                               let uu____5774 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               let uu____5775 =
                                                 let uu____5777 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     t2
                                                    in
                                                 let uu____5778 =
                                                   let uu____5780 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____5781 =
                                                     let uu____5783 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head2
                                                        in
                                                     let uu____5784 =
                                                       let uu____5786 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____5787 =
                                                         let uu____5789 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____5789]  in
                                                       uu____5786 ::
                                                         uu____5787
                                                        in
                                                     uu____5783 :: uu____5784
                                                      in
                                                   uu____5780 :: uu____5781
                                                    in
                                                 uu____5777 :: uu____5778  in
                                               uu____5774 :: uu____5775  in
                                             (bind_inst, uu____5772)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____5762
                                            in
                                         FStar_Syntax_Syntax.mk uu____5761
                                          in
                                       uu____5758 None
                                         t2.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____5801 = FStar_List.tl stack1
                                        in
                                     norm cfg env uu____5801 reified
                                 | FStar_Util.Inr uu____5802 ->
                                     failwith
                                       "Cannot reify a top-level let binding"))
                       | FStar_Syntax_Syntax.Tm_app (head2,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____5820 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____5820 with
                            | (uu____5821,bind_repr) ->
                                let maybe_unfold_action head3 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____5844 =
                                        let uu____5845 =
                                          FStar_Syntax_Subst.compress t3  in
                                        uu____5845.FStar_Syntax_Syntax.n  in
                                      match uu____5844 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____5851) -> t4
                                      | uu____5856 -> head3  in
                                    let uu____5857 =
                                      let uu____5858 =
                                        FStar_Syntax_Subst.compress t4  in
                                      uu____5858.FStar_Syntax_Syntax.n  in
                                    match uu____5857 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____5863 -> None  in
                                  let uu____5864 = maybe_extract_fv head3  in
                                  match uu____5864 with
                                  | Some x when
                                      let uu____5870 =
                                        FStar_Syntax_Syntax.lid_of_fv x  in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____5870
                                      ->
                                      let head4 = norm cfg env [] head3  in
                                      let action_unfolded =
                                        let uu____5874 =
                                          maybe_extract_fv head4  in
                                        match uu____5874 with
                                        | Some uu____5877 -> Some true
                                        | uu____5878 -> Some false  in
                                      (head4, action_unfolded)
                                  | uu____5881 -> (head3, None)  in
                                let rec bind_on_lift args1 acc =
                                  match args1 with
                                  | [] ->
                                      (match FStar_List.rev acc with
                                       | [] ->
                                           failwith
                                             "bind_on_lift should be always called with a non-empty list"
                                       | (head3,uu____5928)::args2 ->
                                           let uu____5943 =
                                             maybe_unfold_action head3  in
                                           (match uu____5943 with
                                            | (head4,found_action) ->
                                                let mk1 tm =
                                                  (FStar_Syntax_Syntax.mk tm)
                                                    None
                                                    t2.FStar_Syntax_Syntax.pos
                                                   in
                                                let body =
                                                  mk1
                                                    (FStar_Syntax_Syntax.Tm_app
                                                       (head4, args2))
                                                   in
                                                (match found_action with
                                                 | None  ->
                                                     FStar_Syntax_Util.mk_reify
                                                       body
                                                 | Some (false ) ->
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_meta
                                                          (body,
                                                            (FStar_Syntax_Syntax.Meta_monadic
                                                               (m1, t2))))
                                                 | Some (true ) -> body)))
                                  | (e,q)::es ->
                                      let uu____5989 =
                                        let uu____5990 =
                                          FStar_Syntax_Subst.compress e  in
                                        uu____5990.FStar_Syntax_Syntax.n  in
                                      (match uu____5989 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (m11,m2,t'))
                                           when
                                           Prims.op_Negation
                                             (FStar_Syntax_Util.is_pure_effect
                                                m11)
                                           ->
                                           let x =
                                             FStar_Syntax_Syntax.gen_bv
                                               "monadic_app_var" None t'
                                              in
                                           let body =
                                             let uu____6011 =
                                               let uu____6017 =
                                                 let uu____6020 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x
                                                    in
                                                 (uu____6020, q)  in
                                               uu____6017 :: acc  in
                                             bind_on_lift es uu____6011  in
                                           let lifted_e0 =
                                             reify_lift cfg.tcenv e0 m11 m2
                                               t'
                                              in
                                           let continuation =
                                             FStar_Syntax_Util.abs
                                               [(x, None)] body
                                               (Some
                                                  (FStar_Util.Inr (m2, [])))
                                              in
                                           let bind_inst =
                                             let uu____6044 =
                                               let uu____6045 =
                                                 FStar_Syntax_Subst.compress
                                                   bind_repr
                                                  in
                                               uu____6045.FStar_Syntax_Syntax.n
                                                in
                                             match uu____6044 with
                                             | FStar_Syntax_Syntax.Tm_uinst
                                                 (bind1,uu____6051::uu____6052::[])
                                                 ->
                                                 let uu____6058 =
                                                   let uu____6061 =
                                                     let uu____6062 =
                                                       let uu____6067 =
                                                         let uu____6069 =
                                                           (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.tcenv t'
                                                            in
                                                         let uu____6070 =
                                                           let uu____6072 =
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv t2
                                                              in
                                                           [uu____6072]  in
                                                         uu____6069 ::
                                                           uu____6070
                                                          in
                                                       (bind1, uu____6067)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_uinst
                                                       uu____6062
                                                      in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____6061
                                                    in
                                                 uu____6058 None
                                                   e0.FStar_Syntax_Syntax.pos
                                             | uu____6084 ->
                                                 failwith
                                                   "NIY : Reification of indexed effects"
                                              in
                                           let uu____6087 =
                                             let uu____6090 =
                                               let uu____6091 =
                                                 let uu____6101 =
                                                   let uu____6103 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t'
                                                      in
                                                   let uu____6104 =
                                                     let uu____6106 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t2
                                                        in
                                                     let uu____6107 =
                                                       let uu____6109 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____6110 =
                                                         let uu____6112 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             lifted_e0
                                                            in
                                                         let uu____6113 =
                                                           let uu____6115 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let uu____6116 =
                                                             let uu____6118 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 continuation
                                                                in
                                                             [uu____6118]  in
                                                           uu____6115 ::
                                                             uu____6116
                                                            in
                                                         uu____6112 ::
                                                           uu____6113
                                                          in
                                                       uu____6109 ::
                                                         uu____6110
                                                        in
                                                     uu____6106 :: uu____6107
                                                      in
                                                   uu____6103 :: uu____6104
                                                    in
                                                 (bind_inst, uu____6101)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____6091
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____6090
                                              in
                                           uu____6087 None
                                             e0.FStar_Syntax_Syntax.pos
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                            uu____6131)
                                           ->
                                           bind_on_lift es ((e0, q) :: acc)
                                       | uu____6147 ->
                                           bind_on_lift es ((e, q) :: acc))
                                   in
                                let binded_head =
                                  let uu____6153 =
                                    let uu____6157 =
                                      FStar_Syntax_Syntax.as_arg head2  in
                                    uu____6157 :: args  in
                                  bind_on_lift uu____6153 []  in
                                let uu____6162 = FStar_List.tl stack1  in
                                norm cfg env uu____6162 binded_head)
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted = reify_lift cfg.tcenv e msrc mtgt t'
                              in
                           norm cfg env stack1 lifted
                       | uu____6176 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6185;
                             FStar_Syntax_Syntax.pos = uu____6186;
                             FStar_Syntax_Syntax.vars = uu____6187;_},uu____6188,uu____6189))::uu____6190
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6196 -> false  in
                    if should_reify
                    then
                      let uu____6197 = FStar_List.tl stack1  in
                      let uu____6198 = reify_lift cfg.tcenv head1 m1 m' t2
                         in
                      norm cfg env uu____6197 uu____6198
                    else
                      (let uu____6200 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations))
                          in
                       if uu____6200
                       then
                         let stack2 =
                           (Steps ((cfg.steps), (cfg.delta_level))) :: stack1
                            in
                         let cfg1 =
                           let uu___162_6205 = cfg  in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___162_6205.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only]
                           }  in
                         norm cfg1 env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t2)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack2)
                           head1
                       else
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m1, m', t2)),
                                 (head1.FStar_Syntax_Syntax.pos))) :: stack1)
                           head1)
                | uu____6211 ->
                    (match stack1 with
                     | uu____6212::uu____6213 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____6217)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____6232 -> norm cfg env stack1 head1)
                     | uu____6233 ->
                         let head2 = norm cfg env [] head1  in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____6243 =
                                 norm_pattern_args cfg env args  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6243
                           | uu____6250 -> m  in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack1 t2)))

and reify_lift :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
              let uu____6264 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____6264 with
              | (uu____6265,return_repr) ->
                  let return_inst =
                    let uu____6272 =
                      let uu____6273 =
                        FStar_Syntax_Subst.compress return_repr  in
                      uu____6273.FStar_Syntax_Syntax.n  in
                    match uu____6272 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____6279::[])
                        ->
                        let uu____6285 =
                          let uu____6288 =
                            let uu____6289 =
                              let uu____6294 =
                                let uu____6296 =
                                  env.FStar_TypeChecker_Env.universe_of env t
                                   in
                                [uu____6296]  in
                              (return_tm, uu____6294)  in
                            FStar_Syntax_Syntax.Tm_uinst uu____6289  in
                          FStar_Syntax_Syntax.mk uu____6288  in
                        uu____6285 None e.FStar_Syntax_Syntax.pos
                    | uu____6308 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  let uu____6311 =
                    let uu____6314 =
                      let uu____6315 =
                        let uu____6325 =
                          let uu____6327 = FStar_Syntax_Syntax.as_arg t  in
                          let uu____6328 =
                            let uu____6330 = FStar_Syntax_Syntax.as_arg e  in
                            [uu____6330]  in
                          uu____6327 :: uu____6328  in
                        (return_inst, uu____6325)  in
                      FStar_Syntax_Syntax.Tm_app uu____6315  in
                    FStar_Syntax_Syntax.mk uu____6314  in
                  uu____6311 None e.FStar_Syntax_Syntax.pos
            else failwith "NYI: non pure monadic lift normalisation"

and norm_pattern_args :
  cfg ->
    env ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list
        Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list
          Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____6372  ->
                   match uu____6372 with
                   | (a,imp) ->
                       let uu____6379 = norm cfg env [] a  in
                       (uu____6379, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp  in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___163_6394 = comp1  in
            let uu____6397 =
              let uu____6398 =
                let uu____6404 = norm cfg env [] t  in
                let uu____6405 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____6404, uu____6405)  in
              FStar_Syntax_Syntax.Total uu____6398  in
            {
              FStar_Syntax_Syntax.n = uu____6397;
              FStar_Syntax_Syntax.tk = (uu___163_6394.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___163_6394.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___163_6394.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___164_6420 = comp1  in
            let uu____6423 =
              let uu____6424 =
                let uu____6430 = norm cfg env [] t  in
                let uu____6431 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____6430, uu____6431)  in
              FStar_Syntax_Syntax.GTotal uu____6424  in
            {
              FStar_Syntax_Syntax.n = uu____6423;
              FStar_Syntax_Syntax.tk = (uu___164_6420.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___164_6420.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___164_6420.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6462  ->
                      match uu____6462 with
                      | (a,i) ->
                          let uu____6469 = norm cfg env [] a  in
                          (uu____6469, i)))
               in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___134_6474  ->
                      match uu___134_6474 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____6478 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____6478
                      | f -> f))
               in
            let uu___165_6482 = comp1  in
            let uu____6485 =
              let uu____6486 =
                let uu___166_6487 = ct  in
                let uu____6488 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____6489 = norm_args ct.FStar_Syntax_Syntax.effect_args
                   in
                {
                  FStar_Syntax_Syntax.comp_typ_name =
                    (uu___166_6487.FStar_Syntax_Syntax.comp_typ_name);
                  FStar_Syntax_Syntax.comp_univs = uu____6488;
                  FStar_Syntax_Syntax.effect_args = uu____6489;
                  FStar_Syntax_Syntax.flags = flags
                }  in
              FStar_Syntax_Syntax.Comp uu____6486  in
            {
              FStar_Syntax_Syntax.n = uu____6485;
              FStar_Syntax_Syntax.tk = (uu___165_6482.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___165_6482.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___165_6482.FStar_Syntax_Syntax.vars)
            }

and ghost_to_pure_aux :
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
            (let uu___167_6506 = cfg  in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___167_6506.tcenv);
               delta_level = (uu___167_6506.delta_level)
             }) env [] t
           in
        let non_info t =
          let uu____6511 = norm1 t  in
          FStar_TypeChecker_Env.non_informative cfg.tcenv uu____6511  in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____6514 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___168_6528 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___168_6528.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___168_6528.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_6528.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.comp_typ_name
               in
            let uu____6538 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (let uu____6539 =
                   FStar_TypeChecker_Env.result_typ cfg.tcenv c  in
                 non_info uu____6539)
               in
            if uu____6538
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.comp_typ_name
                with
                | Some pure_eff ->
                    let uu___169_6544 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_typ_name = pure_eff;
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___169_6544.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___169_6544.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___169_6544.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                       in
                    let uu___170_6546 = ct1  in
                    {
                      FStar_Syntax_Syntax.comp_typ_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___170_6546.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___170_6546.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___170_6546.FStar_Syntax_Syntax.flags)
                    }
                 in
              let uu___171_6547 = c  in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___171_6547.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___171_6547.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___171_6547.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____6553 -> c

and norm_binder :
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____6556  ->
        match uu____6556 with
        | (x,imp) ->
            let uu____6559 =
              let uu___172_6560 = x  in
              let uu____6561 = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___172_6560.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___172_6560.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____6561
              }  in
            (uu____6559, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6567 =
          FStar_List.fold_left
            (fun uu____6574  ->
               fun b  ->
                 match uu____6574 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs
           in
        match uu____6567 with | (nbs,uu____6591) -> FStar_List.rev nbs

and norm_lcomp_opt :
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
            let flags = filter_out_lcomp_cflags lc  in
            let uu____6608 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
            if uu____6608
            then
              let u =
                let uu____6613 =
                  FStar_List.hd lc.FStar_Syntax_Syntax.lcomp_univs  in
                norm_universe cfg env uu____6613  in
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.lcomp_res_typ
                 in
              let c =
                let uu____6616 = FStar_Syntax_Util.is_total_lcomp lc  in
                if uu____6616
                then FStar_Syntax_Syntax.mk_Total' t (Some u)
                else FStar_Syntax_Syntax.mk_GTotal' t (Some u)  in
              let uu____6618 =
                let uu____6621 =
                  let uu____6622 = FStar_Syntax_Util.comp_set_flags c flags
                     in
                  FStar_TypeChecker_Env.lcomp_of_comp cfg.tcenv uu____6622
                   in
                FStar_Util.Inl uu____6621  in
              Some uu____6618
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.lcomp_name), flags))
        | uu____6635 -> lopt

and rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          match stack1 with
          | [] -> t
          | (Debug tm)::stack2 ->
              ((let uu____6647 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms")
                   in
                if uu____6647
                then
                  let uu____6648 = FStar_Syntax_Print.term_to_string tm  in
                  let uu____6649 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____6648
                    uu____6649
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,dl))::stack2 ->
              rebuild
                (let uu___173_6657 = cfg  in
                 { steps = s; tcenv = (uu___173_6657.tcenv); delta_level = dl
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____6677  ->
                    let uu____6678 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" uu____6678);
               rebuild cfg env stack2 t)
          | (Let (env',bs,lb,r))::stack2 ->
              let body = FStar_Syntax_Subst.close bs t  in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) None r
                 in
              rebuild cfg env' stack2 t1
          | (Abs (env',bs,env'',lopt,r))::stack2 ->
              let bs1 = norm_binders cfg env' bs  in
              let lopt1 = norm_lcomp_opt cfg env'' lopt  in
              let uu____6715 =
                let uu___174_6716 = FStar_Syntax_Util.abs bs1 t lopt1  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___174_6716.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___174_6716.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___174_6716.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack2 uu____6715
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____6738),aq,r))::stack2 ->
              (log cfg
                 (fun uu____6754  ->
                    let uu____6755 = FStar_Syntax_Print.term_to_string tm  in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____6755);
               if FStar_List.contains (Exclude Iota) cfg.steps
               then
                 (if FStar_List.contains WHNF cfg.steps
                  then
                    let arg = closure_as_term cfg env1 tm  in
                    let t1 =
                      FStar_Syntax_Syntax.extend_app t (arg, aq) None r  in
                    rebuild cfg env1 stack2 t1
                  else
                    (let stack3 = (App (t, aq, r)) :: stack2  in
                     norm cfg env1 stack3 tm))
               else
                 (let uu____6766 = FStar_ST.read m  in
                  match uu____6766 with
                  | None  ->
                      if FStar_List.contains WHNF cfg.steps
                      then
                        let arg = closure_as_term cfg env1 tm  in
                        let t1 =
                          FStar_Syntax_Syntax.extend_app t (arg, aq) None r
                           in
                        rebuild cfg env1 stack2 t1
                      else
                        (let stack3 = (MemoLazy m) :: (App (t, aq, r)) ::
                           stack2  in
                         norm cfg env1 stack3 tm)
                  | Some (uu____6792,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r  in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r
                 in
              let uu____6814 = maybe_simplify cfg.steps t1  in
              rebuild cfg env stack2 uu____6814
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____6821  ->
                    let uu____6822 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____6822);
               (let scrutinee = t  in
                let norm_and_rebuild_match uu____6827 =
                  let whnf = FStar_List.contains WHNF cfg.steps  in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___135_6834  ->
                              match uu___135_6834 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____6835 -> false))
                       in
                    let steps' =
                      let uu____6838 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations)
                         in
                      if uu____6838
                      then [Exclude Zeta]
                      else [Exclude Iota; Exclude Zeta]  in
                    let uu___175_6841 = cfg  in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___175_6841.tcenv);
                      delta_level = new_delta
                    }  in
                  let norm_or_whnf env2 t1 =
                    if whnf
                    then closure_as_term cfg_exclude_iota_zeta env2 t1
                    else norm cfg_exclude_iota_zeta env2 [] t1  in
                  let rec norm_pat env2 p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____6875 ->
                        (p, env2)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                        let uu____6895 = norm_pat env2 hd1  in
                        (match uu____6895 with
                         | (hd2,env') ->
                             let tl2 =
                               FStar_All.pipe_right tl1
                                 (FStar_List.map
                                    (fun p1  ->
                                       let uu____6931 = norm_pat env2 p1  in
                                       Prims.fst uu____6931))
                                in
                             ((let uu___176_6943 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd2 :: tl2));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___176_6943.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___176_6943.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____6960 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____6994  ->
                                  fun uu____6995  ->
                                    match (uu____6994, uu____6995) with
                                    | ((pats1,env3),(p1,b)) ->
                                        let uu____7060 = norm_pat env3 p1  in
                                        (match uu____7060 with
                                         | (p2,env4) ->
                                             (((p2, b) :: pats1), env4)))
                               ([], env2))
                           in
                        (match uu____6960 with
                         | (pats1,env3) ->
                             ((let uu___177_7126 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats1)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___177_7126.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___177_7126.FStar_Syntax_Syntax.p)
                               }), env3))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x1 =
                          let uu___178_7140 = x  in
                          let uu____7141 =
                            norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___178_7140.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___178_7140.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7141
                          }  in
                        ((let uu___179_7147 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x1);
                            FStar_Syntax_Syntax.ty =
                              (uu___179_7147.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___179_7147.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env2))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x1 =
                          let uu___180_7152 = x  in
                          let uu____7153 =
                            norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___180_7152.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___180_7152.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7153
                          }  in
                        ((let uu___181_7159 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x1);
                            FStar_Syntax_Syntax.ty =
                              (uu___181_7159.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___181_7159.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env2))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                        let x1 =
                          let uu___182_7169 = x  in
                          let uu____7170 =
                            norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___182_7169.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___182_7169.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7170
                          }  in
                        let t2 = norm_or_whnf env2 t1  in
                        ((let uu___183_7177 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                            FStar_Syntax_Syntax.ty =
                              (uu___183_7177.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___183_7177.FStar_Syntax_Syntax.p)
                          }), env2)
                     in
                  let branches1 =
                    match env1 with
                    | [] when whnf -> branches
                    | uu____7181 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch1  ->
                                let uu____7184 =
                                  FStar_Syntax_Subst.open_branch branch1  in
                                match uu____7184 with
                                | (p,wopt,e) ->
                                    let uu____7202 = norm_pat env1 p  in
                                    (match uu____7202 with
                                     | (p1,env2) ->
                                         let wopt1 =
                                           match wopt with
                                           | None  -> None
                                           | Some w ->
                                               let uu____7226 =
                                                 norm_or_whnf env2 w  in
                                               Some uu____7226
                                            in
                                         let e1 = norm_or_whnf env2 e  in
                                         FStar_Syntax_Util.branch
                                           (p1, wopt1, e1))))
                     in
                  let uu____7231 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                      r
                     in
                  rebuild cfg env1 stack2 uu____7231  in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____7241) -> is_cons h
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
                  | uu____7252 -> false  in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | None  -> b
                  | Some w ->
                      let then_branch = b  in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r
                         in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch
                   in
                let rec matches_pat scrutinee1 p =
                  let scrutinee2 = FStar_Syntax_Util.unmeta scrutinee1  in
                  let uu____7351 = FStar_Syntax_Util.head_and_args scrutinee2
                     in
                  match uu____7351 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p1  ->
                                  let m = matches_pat scrutinee2 p1  in
                                  match m with
                                  | FStar_Util.Inl uu____7408 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None)
                              in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____7439 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____7451 ->
                                let uu____7452 =
                                  let uu____7453 = is_cons head1  in
                                  Prims.op_Negation uu____7453  in
                                FStar_Util.Inr uu____7452)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____7467 =
                             let uu____7468 =
                               FStar_Syntax_Util.un_uinst head1  in
                             uu____7468.FStar_Syntax_Syntax.n  in
                           (match uu____7467 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____7475 ->
                                let uu____7476 =
                                  let uu____7477 = is_cons head1  in
                                  Prims.op_Negation uu____7477  in
                                FStar_Util.Inr uu____7476))
                
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____7511)::rest_a,(p1,uu____7514)::rest_p) ->
                      let uu____7542 = matches_pat t1 p1  in
                      (match uu____7542 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____7556 -> FStar_Util.Inr false
                 in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____7627 = matches_pat scrutinee1 p1  in
                      (match uu____7627 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____7637  ->
                                 let uu____7638 =
                                   FStar_Syntax_Print.pat_to_string p1  in
                                 let uu____7639 =
                                   let uu____7640 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s
                                      in
                                   FStar_All.pipe_right uu____7640
                                     (FStar_String.concat "; ")
                                    in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____7638 uu____7639);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____7649 =
                                        let uu____7650 =
                                          let uu____7660 =
                                            FStar_Util.mk_ref (Some ([], t1))
                                             in
                                          ([], t1, uu____7660, false)  in
                                        Clos uu____7650  in
                                      uu____7649 :: env2) env1 s
                                in
                             let uu____7683 = guard_when_clause wopt b rest
                                in
                             norm cfg env2 stack2 uu____7683)))
                   in
                let uu____7684 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota))
                   in
                if uu____7684
                then norm_and_rebuild_match ()
                else matches scrutinee branches))

let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___136_7698  ->
                match uu___136_7698 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____7701 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____7705 -> d  in
      { steps = s; tcenv = e; delta_level = d1 }
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____7716 = config s e  in norm uu____7716 [] [] t
  
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____7726 = config s e  in norm_comp uu____7726 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____7733 = config [] env  in norm_universe uu____7733 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____7740 = config [] env  in ghost_to_pure_aux uu____7740 [] c
  
let ghost_to_pure_lcomp :
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
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____7752 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____7752  in
      let uu____7753 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.lcomp_name)
          && (non_info lc.FStar_Syntax_Syntax.lcomp_res_typ)
         in
      if uu____7753
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.lcomp_name
        with
        | Some pure_eff ->
            let uu___184_7755 = lc  in
            {
              FStar_Syntax_Syntax.lcomp_name = pure_eff;
              FStar_Syntax_Syntax.lcomp_univs =
                (uu___184_7755.FStar_Syntax_Syntax.lcomp_univs);
              FStar_Syntax_Syntax.lcomp_indices =
                (uu___184_7755.FStar_Syntax_Syntax.lcomp_indices);
              FStar_Syntax_Syntax.lcomp_res_typ =
                (uu___184_7755.FStar_Syntax_Syntax.lcomp_res_typ);
              FStar_Syntax_Syntax.lcomp_cflags =
                (uu___184_7755.FStar_Syntax_Syntax.lcomp_cflags);
              FStar_Syntax_Syntax.lcomp_as_comp =
                ((fun uu____7756  ->
                    let uu____7757 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                       in
                    ghost_to_pure env uu____7757))
            }
        | None  -> lc
      else lc
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____7765 = normalize [AllowUnboundUniverses] env t  in
      FStar_Syntax_Print.term_to_string uu____7765
  
let comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____7772 =
        let uu____7773 = config [AllowUnboundUniverses] env  in
        norm_comp uu____7773 [] c  in
      FStar_Syntax_Print.comp_to_string uu____7772
  
let normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0  in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____7810 =
                     let uu____7811 =
                       let uu____7816 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____7816)  in
                     FStar_Syntax_Syntax.Tm_refine uu____7811  in
                   mk uu____7810 t01.FStar_Syntax_Syntax.pos
               | uu____7821 -> t2)
          | uu____7822 -> t2  in
        aux t
  
let eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun sort  ->
        let uu____7832 = FStar_Syntax_Util.arrow_formals_comp sort  in
        match uu____7832 with
        | (binders,c) ->
            (match binders with
             | [] -> t
             | uu____7848 ->
                 let uu____7852 =
                   FStar_All.pipe_right binders
                     FStar_Syntax_Util.args_of_binders
                    in
                 (match uu____7852 with
                  | (binders1,args) ->
                      let uu____7862 =
                        (FStar_Syntax_Syntax.mk_Tm_app t args) None
                          t.FStar_Syntax_Syntax.pos
                         in
                      let uu____7867 =
                        let uu____7874 =
                          let uu____7880 =
                            FStar_TypeChecker_Env.lcomp_of_comp env c  in
                          FStar_Util.Inl uu____7880  in
                        Some uu____7874  in
                      FStar_Syntax_Util.abs binders1 uu____7862 uu____7867))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____7895 =
        let uu____7899 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
        (uu____7899, (t.FStar_Syntax_Syntax.n))  in
      match uu____7895 with
      | (Some sort,uu____7906) ->
          let uu____7908 = mk sort t.FStar_Syntax_Syntax.pos  in
          eta_expand_with_type env t uu____7908
      | (uu____7909,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____7913 ->
          let uu____7917 = FStar_Syntax_Util.head_and_args t  in
          (match uu____7917 with
           | (head1,args) ->
               let uu____7943 =
                 let uu____7944 = FStar_Syntax_Subst.compress head1  in
                 uu____7944.FStar_Syntax_Syntax.n  in
               (match uu____7943 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____7947,thead) ->
                    let uu____7961 =
                      FStar_Syntax_Util.arrow_formals_comp thead  in
                    (match uu____7961 with
                     | (formals,uu____7968) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____7986 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___185_7990 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___185_7990.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___185_7990.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___185_7990.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___185_7990.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___185_7990.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___185_7990.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___185_7990.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___185_7990.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___185_7990.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___185_7990.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___185_7990.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___185_7990.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___185_7990.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___185_7990.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___185_7990.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___185_7990.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___185_7990.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___185_7990.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___185_7990.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___185_7990.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___185_7990.FStar_TypeChecker_Env.qname_and_index)
                                 }) t
                               in
                            match uu____7986 with
                            | (uu____7991,ty,uu____7993) ->
                                eta_expand_with_type env t ty))
                | uu____7994 ->
                    let uu____7995 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___186_7999 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___186_7999.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___186_7999.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___186_7999.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___186_7999.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___186_7999.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___186_7999.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___186_7999.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___186_7999.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___186_7999.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___186_7999.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___186_7999.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___186_7999.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___186_7999.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___186_7999.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___186_7999.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___186_7999.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___186_7999.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___186_7999.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___186_7999.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___186_7999.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___186_7999.FStar_TypeChecker_Env.qname_and_index)
                         }) t
                       in
                    (match uu____7995 with
                     | (uu____8000,ty,uu____8002) ->
                         eta_expand_with_type env t ty)))
  