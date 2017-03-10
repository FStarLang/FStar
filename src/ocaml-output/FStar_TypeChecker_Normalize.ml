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
  fun uu___124_174  ->
    match uu___124_174 with
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
    let _0_304 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right _0_304 (FStar_String.concat "; ")
  
let stack_elt_to_string : stack_elt -> Prims.string =
  fun uu___125_591  ->
    match uu___125_591 with
    | Arg (c,uu____593,uu____594) ->
        let _0_305 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" _0_305
    | MemoLazy uu____595 -> "MemoLazy"
    | Abs (uu____599,bs,uu____601,uu____602,uu____603) ->
        let _0_306 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" _0_306
    | UnivArgs uu____614 -> "UnivArgs"
    | Match uu____618 -> "Match"
    | App (t,uu____623,uu____624) ->
        let _0_307 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" _0_307
    | Meta (m,uu____626) -> "Meta"
    | Let uu____627 -> "Let"
    | Steps (s,uu____633) -> "Steps"
    | Debug t ->
        let _0_308 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" _0_308
  
let stack_to_string : stack_elt Prims.list -> Prims.string =
  fun s  ->
    let _0_309 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right _0_309 (FStar_String.concat "; ")
  
let log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____654 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____654 then f () else ()
  
let is_empty uu___126_663 =
  match uu___126_663 with | [] -> true | uu____665 -> false 
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____683 ->
      failwith
        (let _0_310 = FStar_Syntax_Print.db_to_string x  in
         FStar_Util.format1 "Failed to find %s\n" _0_310)
  
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
          let us = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____714 =
            FStar_List.fold_left
              (fun uu____723  ->
                 fun u  ->
                   match uu____723 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____738 = FStar_Syntax_Util.univ_kernel u  in
                       (match uu____738 with
                        | (k_u,n) ->
                            let uu____747 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____747
                            then (cur_kernel, u, out)
                            else (k_u, u, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us
             in
          match uu____714 with
          | (uu____757,u,out) -> FStar_List.rev (u :: out)  in
        let rec aux u =
          let u = FStar_Syntax_Subst.compress_univ u  in
          match u with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____773 = FStar_List.nth env x  in
                 match uu____773 with
                 | Univ u -> aux u
                 | Dummy  -> [u]
                 | uu____776 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____780 ->
                   let uu____781 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____781
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us =
                let _0_311 = FStar_List.collect aux us  in
                FStar_All.pipe_right _0_311 norm_univs  in
              (match us with
               | u_k::hd::rest ->
                   let rest = hd :: rest  in
                   let uu____800 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____800 with
                    | (FStar_Syntax_Syntax.U_zero ,n) ->
                        let uu____805 =
                          FStar_All.pipe_right rest
                            (FStar_List.for_all
                               (fun u  ->
                                  let uu____808 =
                                    FStar_Syntax_Util.univ_kernel u  in
                                  match uu____808 with
                                  | (uu____811,m) -> n <= m))
                           in
                        if uu____805 then rest else us
                    | uu____815 -> us)
               | uu____818 -> us)
          | FStar_Syntax_Syntax.U_succ u ->
              let _0_313 = aux u  in
              FStar_List.map
                (fun _0_312  -> FStar_Syntax_Syntax.U_succ _0_312) _0_313
           in
        let uu____821 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____821
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____823 = aux u  in
           match uu____823 with
           | []|(FStar_Syntax_Syntax.U_zero )::[] ->
               FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u::[] -> u
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u::[] -> u
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
          (fun uu____920  ->
             let _0_315 = FStar_Syntax_Print.tag_of_term t  in
             let _0_314 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" _0_315 _0_314);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____921 ->
             let t = FStar_Syntax_Subst.compress t  in
             (match t.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____924 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t
              | FStar_Syntax_Syntax.Tm_uvar uu____948 -> t
              | FStar_Syntax_Syntax.Tm_type u ->
                  let _0_316 =
                    FStar_Syntax_Syntax.Tm_type (norm_universe cfg env u)  in
                  mk _0_316 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
                  let _0_317 = FStar_List.map (norm_universe cfg env) us  in
                  FStar_Syntax_Syntax.mk_Tm_uinst t _0_317
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____965 = lookup_bvar env x  in
                  (match uu____965 with
                   | Univ uu____966 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t
                   | Clos (env,t0,r,uu____970) -> closure_as_term cfg env t0)
              | FStar_Syntax_Syntax.Tm_app (head,args) ->
                  let head = closure_as_term_delayed cfg env head  in
                  let args = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head, args))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1038 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1038 with
                   | (bs,env) ->
                       let body = closure_as_term_delayed cfg env body  in
                       let _0_319 =
                         FStar_Syntax_Syntax.Tm_abs
                           (let _0_318 = close_lcomp_opt cfg env lopt  in
                            (bs, body, _0_318))
                          in
                       mk _0_319 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1081 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1081 with
                   | (bs,env) ->
                       let c = close_comp cfg env c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                         t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1112 =
                    let _0_321 =
                      let _0_320 = FStar_Syntax_Syntax.mk_binder x  in
                      [_0_320]  in
                    closures_as_binders_delayed cfg env _0_321  in
                  (match uu____1112 with
                   | (x,env) ->
                       let phi = closure_as_term_delayed cfg env phi  in
                       let _0_324 =
                         FStar_Syntax_Syntax.Tm_refine
                           (let _0_323 =
                              let _0_322 = FStar_List.hd x  in
                              FStar_All.pipe_right _0_322 Prims.fst  in
                            (_0_323, phi))
                          in
                       mk _0_324 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,lopt)
                  ->
                  let _0_329 =
                    FStar_Syntax_Syntax.Tm_ascribed
                      (let _0_328 = closure_as_term_delayed cfg env t1  in
                       let _0_327 =
                         let _0_326 = closure_as_term_delayed cfg env t2  in
                         FStar_All.pipe_left
                           (fun _0_325  -> FStar_Util.Inl _0_325) _0_326
                          in
                       (_0_328, _0_327, lopt))
                     in
                  mk _0_329 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,lopt) ->
                  let _0_334 =
                    FStar_Syntax_Syntax.Tm_ascribed
                      (let _0_333 = closure_as_term_delayed cfg env t1  in
                       let _0_332 =
                         let _0_331 = close_comp cfg env c  in
                         FStar_All.pipe_left
                           (fun _0_330  -> FStar_Util.Inr _0_330) _0_331
                          in
                       (_0_333, _0_332, lopt))
                     in
                  mk _0_334 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let _0_337 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_336 = closure_as_term_delayed cfg env t'  in
                       let _0_335 =
                         FStar_Syntax_Syntax.Meta_pattern
                           (FStar_All.pipe_right args
                              (FStar_List.map
                                 (closures_as_args_delayed cfg env)))
                          in
                       (_0_336, _0_335))
                     in
                  mk _0_337 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let _0_341 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_340 = closure_as_term_delayed cfg env t'  in
                       let _0_339 =
                         FStar_Syntax_Syntax.Meta_monadic
                           (let _0_338 =
                              closure_as_term_delayed cfg env tbody  in
                            (m, _0_338))
                          in
                       (_0_340, _0_339))
                     in
                  mk _0_341 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let _0_345 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_344 = closure_as_term_delayed cfg env t'  in
                       let _0_343 =
                         FStar_Syntax_Syntax.Meta_monadic_lift
                           (let _0_342 =
                              closure_as_term_delayed cfg env tbody  in
                            (m1, m2, _0_342))
                          in
                       (_0_344, _0_343))
                     in
                  mk _0_345 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let _0_347 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_346 = closure_as_term_delayed cfg env t'  in
                       (_0_346, m))
                     in
                  mk _0_347 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env =
                    FStar_List.fold_left
                      (fun env  -> fun uu____1313  -> Dummy :: env) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef  in
                  let body =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1324 -> body
                    | FStar_Util.Inl uu____1325 ->
                        closure_as_term cfg (Dummy :: env0) body
                     in
                  let lb =
                    let uu___138_1327 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___138_1327.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___138_1327.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___138_1327.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    }  in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1334,lbs),body) ->
                  let norm_one_lb env lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1358  -> fun env  -> Dummy :: env)
                        lb.FStar_Syntax_Syntax.lbunivs env
                       in
                    let env =
                      let uu____1363 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____1363
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1367  -> fun env  -> Dummy :: env) lbs
                          env_univs
                       in
                    let uu___139_1370 = lb  in
                    let _0_349 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let _0_348 =
                      closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___139_1370.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___139_1370.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = _0_349;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___139_1370.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = _0_348
                    }  in
                  let lbs =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1379  -> fun env  -> Dummy :: env) lbs env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head,branches) ->
                  let head = closure_as_term cfg env head  in
                  let norm_one_branch env uu____1434 =
                    match uu____1434 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1480 ->
                              (p, env)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                              let uu____1500 = norm_pat env hd  in
                              (match uu____1500 with
                               | (hd,env') ->
                                   let tl =
                                     FStar_All.pipe_right tl
                                       (FStar_List.map
                                          (fun p  ->
                                             Prims.fst (norm_pat env p)))
                                      in
                                   ((let uu___140_1542 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd ::
                                            tl));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___140_1542.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___140_1542.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1559 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1593  ->
                                        fun uu____1594  ->
                                          match (uu____1593, uu____1594) with
                                          | ((pats,env),(p,b)) ->
                                              let uu____1659 = norm_pat env p
                                                 in
                                              (match uu____1659 with
                                               | (p,env) ->
                                                   (((p, b) :: pats), env)))
                                     ([], env))
                                 in
                              (match uu____1559 with
                               | (pats,env) ->
                                   ((let uu___141_1725 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___141_1725.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___141_1725.FStar_Syntax_Syntax.p)
                                     }), env))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x =
                                let uu___142_1739 = x  in
                                let _0_350 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___142_1739.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___142_1739.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_350
                                }  in
                              ((let uu___143_1743 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___143_1743.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___143_1743.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x =
                                let uu___144_1748 = x  in
                                let _0_351 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___144_1748.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___144_1748.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_351
                                }  in
                              ((let uu___145_1752 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___145_1752.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___145_1752.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                              let x =
                                let uu___146_1762 = x  in
                                let _0_352 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___146_1762.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___146_1762.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_352
                                }  in
                              let t = closure_as_term cfg env t  in
                              ((let uu___147_1767 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___147_1767.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___147_1767.FStar_Syntax_Syntax.p)
                                }), env)
                           in
                        let uu____1770 = norm_pat env pat  in
                        (match uu____1770 with
                         | (pat,env) ->
                             let w_opt =
                               match w_opt with
                               | None  -> None
                               | Some w -> Some (closure_as_term cfg env w)
                                in
                             let tm = closure_as_term cfg env tm  in
                             (pat, w_opt, tm))
                     in
                  let _0_354 =
                    FStar_Syntax_Syntax.Tm_match
                      (let _0_353 =
                         FStar_All.pipe_right branches
                           (FStar_List.map (norm_one_branch env))
                          in
                       (head, _0_353))
                     in
                  mk _0_354 t.FStar_Syntax_Syntax.pos))

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
        | uu____1843 -> closure_as_term cfg env t

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
        | uu____1859 ->
            FStar_List.map
              (fun uu____1869  ->
                 match uu____1869 with
                 | (x,imp) ->
                     let _0_355 = closure_as_term_delayed cfg env x  in
                     (_0_355, imp)) args

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
        let uu____1893 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____1917  ->
                  fun uu____1918  ->
                    match (uu____1917, uu____1918) with
                    | ((env,out),(b,imp)) ->
                        let b =
                          let uu___148_1962 = b  in
                          let _0_356 =
                            closure_as_term_delayed cfg env
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___148_1962.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___148_1962.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_356
                          }  in
                        let env = Dummy :: env  in (env, ((b, imp) :: out)))
               (env, []))
           in
        match uu____1893 with | (env,bs) -> ((FStar_List.rev bs), env)

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
        | uu____2007 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let _0_358 = closure_as_term_delayed cfg env t  in
                 let _0_357 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 FStar_Syntax_Syntax.mk_Total' _0_358 _0_357
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let _0_360 = closure_as_term_delayed cfg env t  in
                 let _0_359 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 FStar_Syntax_Syntax.mk_GTotal' _0_360 _0_359
             | FStar_Syntax_Syntax.Comp c ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c.FStar_Syntax_Syntax.effect_args
                    in
                 let flags =
                   FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___127_2041  ->
                           match uu___127_2041 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               FStar_Syntax_Syntax.DECREASES
                                 (closure_as_term_delayed cfg env t)
                           | f -> f))
                    in
                 FStar_Syntax_Syntax.mk_Comp
                   (let uu___149_2046 = c  in
                    let _0_361 =
                      FStar_List.map (norm_universe cfg env)
                        c.FStar_Syntax_Syntax.comp_univs
                       in
                    {
                      FStar_Syntax_Syntax.comp_univs = _0_361;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___149_2046.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ = rt;
                      FStar_Syntax_Syntax.effect_args = args;
                      FStar_Syntax_Syntax.flags = flags
                    }))

and filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___128_2050  ->
            match uu___128_2050 with
            | FStar_Syntax_Syntax.DECREASES uu____2051 -> false
            | uu____2054 -> true))

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
            let uu____2082 = FStar_Syntax_Util.is_total_lcomp lc  in
            if uu____2082
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2099 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
               if uu____2099
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2125 -> lopt

let arith_ops :
  (FStar_Ident.lident * (Prims.int -> Prims.int -> FStar_Const.sconst))
    Prims.list
  =
  let int_as_const i =
    FStar_Const.Const_int
      (let _0_362 = FStar_Util.string_of_int i  in (_0_362, None))
     in
  let bool_as_const b = FStar_Const.Const_bool b  in
  let _0_371 =
    FStar_List.flatten
      (FStar_List.map
         (fun m  ->
            let _0_370 =
              let _0_363 = FStar_Syntax_Const.p2l ["FStar"; m; "add"]  in
              (_0_363, (fun x  -> fun y  -> int_as_const (x + y)))  in
            let _0_369 =
              let _0_368 =
                let _0_364 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"]  in
                (_0_364, (fun x  -> fun y  -> int_as_const (x - y)))  in
              let _0_367 =
                let _0_366 =
                  let _0_365 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"]  in
                  (_0_365, (fun x  -> fun y  -> int_as_const (x * y)))  in
                [_0_366]  in
              _0_368 :: _0_367  in
            _0_370 :: _0_369)
         ["Int8";
         "UInt8";
         "Int16";
         "UInt16";
         "Int32";
         "UInt32";
         "Int64";
         "UInt64";
         "UInt128"])
     in
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
      ((fun x  -> fun y  -> int_as_const (x mod y))))] _0_371
  
let un_ops :
  (FStar_Ident.lident *
    (Prims.string ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax))
    Prims.list
  =
  let mk x = mk x FStar_Range.dummyRange  in
  let name x =
    mk
      (FStar_Syntax_Syntax.Tm_fvar
         (let _0_372 = FStar_Syntax_Const.p2l x  in
          FStar_Syntax_Syntax.lid_as_fv _0_372
            FStar_Syntax_Syntax.Delta_constant None))
     in
  let ctor x =
    mk
      (FStar_Syntax_Syntax.Tm_fvar
         (let _0_373 = FStar_Syntax_Const.p2l x  in
          FStar_Syntax_Syntax.lid_as_fv _0_373
            FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor)))
     in
  let _0_390 =
    let _0_389 = FStar_Syntax_Const.p2l ["FStar"; "String"; "list_of_string"]
       in
    (_0_389,
      (fun s  ->
         let _0_388 = FStar_String.list_of_string s  in
         let _0_387 =
           mk
             (FStar_Syntax_Syntax.Tm_app
                (let _0_386 =
                   let _0_382 = ctor ["Prims"; "Nil"]  in
                   FStar_Syntax_Syntax.mk_Tm_uinst _0_382
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let _0_385 =
                   let _0_384 =
                     let _0_383 = name ["FStar"; "Char"; "char"]  in
                     (_0_383, (Some (FStar_Syntax_Syntax.Implicit true)))  in
                   [_0_384]  in
                 (_0_386, _0_385)))
            in
         FStar_List.fold_right
           (fun c  ->
              fun a  ->
                mk
                  (FStar_Syntax_Syntax.Tm_app
                     (let _0_381 =
                        let _0_374 = ctor ["Prims"; "Cons"]  in
                        FStar_Syntax_Syntax.mk_Tm_uinst _0_374
                          [FStar_Syntax_Syntax.U_zero]
                         in
                      let _0_380 =
                        let _0_379 =
                          let _0_375 = name ["FStar"; "Char"; "char"]  in
                          (_0_375,
                            (Some (FStar_Syntax_Syntax.Implicit true)))
                           in
                        let _0_378 =
                          let _0_377 =
                            let _0_376 =
                              mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_char c))
                               in
                            (_0_376, None)  in
                          [_0_377; (a, None)]  in
                        _0_379 :: _0_378  in
                      (_0_381, _0_380)))) _0_388 _0_387))
     in
  [_0_390] 
let reduce_equality :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let is_decidable_equality t =
      let uu____2464 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____2464 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq
      | uu____2466 -> false  in
    let is_propositional_equality t =
      let uu____2471 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____2471 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
      | uu____2473 -> false  in
    match tm.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app
        (op_eq_inst,(_typ,uu____2478)::(a1,uu____2480)::(a2,uu____2482)::[])
        when is_decidable_equality op_eq_inst ->
        let tt =
          let uu____2523 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2523 with
          | FStar_Syntax_Util.Equal  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool true)) tm.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Util.NotEqual  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool false)) tm.FStar_Syntax_Syntax.pos
          | uu____2526 -> tm  in
        tt
    | FStar_Syntax_Syntax.Tm_app (eq2_inst,_::(a1,_)::(a2,_)::[])
      |FStar_Syntax_Syntax.Tm_app (eq2_inst,(a1,_)::(a2,_)::[]) when
        is_propositional_equality eq2_inst ->
        let tt =
          let uu____2598 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2598 with
          | FStar_Syntax_Util.Equal  -> FStar_Syntax_Util.t_true
          | FStar_Syntax_Util.NotEqual  -> FStar_Syntax_Util.t_false
          | uu____2599 -> tm  in
        tt
    | uu____2600 -> tm
  
let find_fv fv ops =
  match fv.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_List.tryFind
        (fun uu____2625  ->
           match uu____2625 with
           | (l,uu____2629) -> FStar_Syntax_Syntax.fv_eq_lid fv l) ops
  | uu____2630 -> None 
let reduce_primops :
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let uu____2647 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops steps)
         in
      if uu____2647
      then tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             (fv,(a1,uu____2655)::(a2,uu____2657)::[]) ->
             let uu____2687 = find_fv fv arith_ops  in
             (match uu____2687 with
              | None  -> tm
              | Some (uu____2707,op) ->
                  let norm i j =
                    let c =
                      let _0_392 = FStar_Util.int_of_string i  in
                      let _0_391 = FStar_Util.int_of_string j  in
                      op _0_392 _0_391  in
                    mk (FStar_Syntax_Syntax.Tm_constant c)
                      tm.FStar_Syntax_Syntax.pos
                     in
                  let uu____2733 =
                    let _0_394 =
                      (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
                       in
                    let _0_393 =
                      (FStar_Syntax_Subst.compress a2).FStar_Syntax_Syntax.n
                       in
                    (_0_394, _0_393)  in
                  (match uu____2733 with
                   | (FStar_Syntax_Syntax.Tm_app
                      (head1,(arg1,uu____2740)::[]),FStar_Syntax_Syntax.Tm_app
                      (head2,(arg2,uu____2743)::[])) ->
                       let uu____2786 =
                         let _0_398 =
                           (FStar_Syntax_Subst.compress head1).FStar_Syntax_Syntax.n
                            in
                         let _0_397 =
                           (FStar_Syntax_Subst.compress head2).FStar_Syntax_Syntax.n
                            in
                         let _0_396 =
                           (FStar_Syntax_Subst.compress arg1).FStar_Syntax_Syntax.n
                            in
                         let _0_395 =
                           (FStar_Syntax_Subst.compress arg2).FStar_Syntax_Syntax.n
                            in
                         (_0_398, _0_397, _0_396, _0_395)  in
                       (match uu____2786 with
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
                            let _0_402 =
                              mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                                tm.FStar_Syntax_Syntax.pos
                               in
                            let _0_401 =
                              let _0_400 =
                                let _0_399 = norm i j  in (_0_399, None)  in
                              [_0_400]  in
                            FStar_Syntax_Util.mk_app _0_402 _0_401
                        | uu____2828 -> tm)
                   | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                      (i,None )),FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (j,None ))) -> norm i j
                   | uu____2845 -> tm))
         | FStar_Syntax_Syntax.Tm_app (fv,(a1,uu____2850)::[]) ->
             let uu____2872 = find_fv fv un_ops  in
             (match uu____2872 with
              | None  -> tm
              | Some (uu____2892,op) ->
                  let uu____2908 =
                    (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
                     in
                  (match uu____2908 with
                   | FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_string (b,uu____2912)) ->
                       op (FStar_Bytes.unicode_bytes_as_string b)
                   | uu____2915 -> tm))
         | uu____2916 -> reduce_equality tm)
  
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
        let uu___150_2941 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___150_2941.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___150_2941.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___150_2941.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____2960 -> None  in
      let simplify arg = ((simp_t (Prims.fst arg)), arg)  in
      let uu____2987 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps)
         in
      if uu____2987
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
             let uu____3031 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid
                in
             if uu____3031
             then
               let uu____3034 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               (match uu____3034 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____3202 -> tm)
             else
               (let uu____3212 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid
                   in
                if uu____3212
                then
                  let uu____3215 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____3215 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____3383 -> tm
                else
                  (let uu____3393 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid
                      in
                   if uu____3393
                   then
                     let uu____3396 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____3396 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____3487)::(uu____3488,(arg,uu____3490))::[]
                         -> arg
                     | uu____3531 -> tm
                   else
                     (let uu____3541 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid
                         in
                      if uu____3541
                      then
                        let uu____3544 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____3544 with
                        | (Some (true ),uu____3579)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____3603)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____3627 -> tm
                      else
                        (let uu____3637 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid)
                            in
                         if uu____3637
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____3682 =
                                 (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                  in
                               (match uu____3682 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____3685::[],body,uu____3687) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____3715 -> tm)
                                | uu____3717 -> tm)
                           | uu____3718 -> tm
                         else reduce_equality tm))))
         | uu____3725 -> tm)
  
let is_norm_request hd args =
  let uu____3740 =
    let _0_403 = (FStar_Syntax_Util.un_uinst hd).FStar_Syntax_Syntax.n  in
    (_0_403, args)  in
  match uu____3740 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3746::uu____3747::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3750::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____3752 -> false 
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____3785 -> failwith "Impossible" 
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t = FStar_Syntax_Subst.compress t  in
          let firstn k l =
            if (FStar_List.length l) < k
            then (l, [])
            else FStar_Util.first_N k l  in
          log cfg
            (fun uu____3904  ->
               let _0_407 = FStar_Syntax_Print.tag_of_term t  in
               let _0_406 = FStar_Syntax_Print.term_to_string t  in
               let _0_405 =
                 stack_to_string
                   (let _0_404 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left Prims.fst _0_404)
                  in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" _0_407 _0_406
                 _0_405);
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____3912 ->
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
               -> rebuild cfg env stack t
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               ((Prims.op_Negation
                   (FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoFullNorm)))
                  && (is_norm_request hd args))
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
                 let uu___151_3971 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___151_3971.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant]
                 }  in
               let stack' = (Debug t) ::
                 (Steps ((cfg.steps), (cfg.delta_level))) :: stack  in
               norm cfg' env stack' tm
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____3975;
                  FStar_Syntax_Syntax.pos = uu____3976;
                  FStar_Syntax_Syntax.vars = uu____3977;_},a1::a2::rest)
               ->
               let uu____4011 = FStar_Syntax_Util.head_and_args t  in
               (match uu____4011 with
                | (hd,uu____4022) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd, [a1])) None
                        t.FStar_Syntax_Syntax.pos
                       in
                    let t =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest))) None
                        t.FStar_Syntax_Syntax.pos
                       in
                    norm cfg env stack t)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4077;
                  FStar_Syntax_Syntax.pos = uu____4078;
                  FStar_Syntax_Syntax.vars = uu____4079;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4102 = FStar_Syntax_Util.head_and_args t  in
               (match uu____4102 with
                | (reify_head,uu____4113) ->
                    let a =
                      FStar_Syntax_Subst.compress
                        (FStar_All.pipe_left FStar_Syntax_Util.unascribe
                           (Prims.fst a))
                       in
                    (match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____4131);
                            FStar_Syntax_Syntax.tk = uu____4132;
                            FStar_Syntax_Syntax.pos = uu____4133;
                            FStar_Syntax_Syntax.vars = uu____4134;_},a::[])
                         -> norm cfg env stack (Prims.fst a)
                     | uu____4159 ->
                         let stack =
                           (App
                              (reify_head, None, (t.FStar_Syntax_Syntax.pos)))
                           :: stack  in
                         norm cfg env stack a))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u = norm_universe cfg env u  in
               let _0_408 =
                 mk (FStar_Syntax_Syntax.Tm_type u) t.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack _0_408
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____4173 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____4173
               then norm cfg env stack t'
               else
                 (let us =
                    UnivArgs
                      (let _0_409 = FStar_List.map (norm_universe cfg env) us
                          in
                       (_0_409, (t.FStar_Syntax_Syntax.pos)))
                     in
                  let stack = us :: stack  in norm cfg env stack t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t  in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___129_4183  ->
                         match uu___129_4183 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l))
                  in
               if Prims.op_Negation should_delta
               then rebuild cfg env stack t
               else
                 (let r_env =
                    let _0_410 = FStar_Syntax_Syntax.range_of_fv f  in
                    FStar_TypeChecker_Env.set_range cfg.tcenv _0_410  in
                  let uu____4187 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  match uu____4187 with
                  | None  ->
                      (log cfg
                         (fun uu____4198  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack t)
                  | Some (us,t) ->
                      (log cfg
                         (fun uu____4204  ->
                            let _0_412 = FStar_Syntax_Print.term_to_string t0
                               in
                            let _0_411 = FStar_Syntax_Print.term_to_string t
                               in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              _0_412 _0_411);
                       (let n = FStar_List.length us  in
                        if n > (Prims.parse_int "0")
                        then
                          match stack with
                          | (UnivArgs (us',uu____4211))::stack ->
                              let env =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env  -> fun u  -> (Univ u) :: env)
                                     env)
                                 in
                              norm cfg env stack t
                          | uu____4224 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack t
                          | uu____4225 ->
                              failwith
                                (let _0_413 =
                                   FStar_Syntax_Print.lid_to_string
                                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 FStar_Util.format1
                                   "Impossible: missing universe instantiation on %s"
                                   _0_413)
                        else norm cfg env stack t)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____4232 = lookup_bvar env x  in
               (match uu____4232 with
                | Univ uu____4233 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____4248 = FStar_ST.read r  in
                      (match uu____4248 with
                       | Some (env,t') ->
                           (log cfg
                              (fun uu____4267  ->
                                 let _0_415 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 let _0_414 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" _0_415
                                   _0_414);
                            (let uu____4268 =
                               (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
                                in
                             match uu____4268 with
                             | FStar_Syntax_Syntax.Tm_abs uu____4269 ->
                                 norm cfg env stack t'
                             | uu____4284 -> rebuild cfg env stack t'))
                       | None  -> norm cfg env ((MemoLazy r) :: stack) t0)
                    else norm cfg env stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____4317)::uu____4318 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4323)::uu____4324 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4330,uu____4331))::stack_rest ->
                    (match c with
                     | Univ uu____4334 -> norm cfg (c :: env) stack_rest t
                     | uu____4335 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____4338::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____4351  ->
                                         let _0_416 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_416);
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
                                           (fun uu___130_4365  ->
                                              match uu___130_4365 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____4366 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____4368  ->
                                         let _0_417 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_417);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____4379  ->
                                         let _0_418 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_418);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____4380 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____4387 ->
                                   let cfg =
                                     let uu___152_4395 = cfg  in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___152_4395.tcenv);
                                       delta_level =
                                         (uu___152_4395.delta_level)
                                     }  in
                                   let _0_419 = closure_as_term cfg env t  in
                                   rebuild cfg env stack _0_419)
                          | uu____4396::tl ->
                              (log cfg
                                 (fun uu____4406  ->
                                    let _0_420 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n" _0_420);
                               (let body =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg (c :: env) stack_rest body))))
                | (Steps (s,dl))::stack ->
                    norm
                      (let uu___153_4427 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___153_4427.tcenv);
                         delta_level = dl
                       }) env stack t
                | (MemoLazy r)::stack ->
                    (set_memo r (env, t);
                     log cfg
                       (fun uu____4440  ->
                          let _0_421 = FStar_Syntax_Print.term_to_string t
                             in
                          FStar_Util.print1 "\tSet memo %s\n" _0_421);
                     norm cfg env stack t)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let _0_422 = closure_as_term cfg env t  in
                      rebuild cfg env stack _0_422
                    else
                      (let uu____4452 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____4452 with
                       | (bs,body,opening) ->
                           let lopt =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let _0_428 =
                                   let _0_426 =
                                     let _0_424 =
                                       let _0_423 =
                                         l.FStar_Syntax_Syntax.comp ()  in
                                       FStar_Syntax_Subst.subst_comp opening
                                         _0_423
                                        in
                                     FStar_All.pipe_right _0_424
                                       FStar_Syntax_Util.lcomp_of_comp
                                      in
                                   FStar_All.pipe_right _0_426
                                     (fun _0_425  -> FStar_Util.Inl _0_425)
                                    in
                                 FStar_All.pipe_right _0_428
                                   (fun _0_427  -> Some _0_427)
                             | uu____4505 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun uu____4519  -> Dummy :: env) env)
                              in
                           (log cfg
                              (fun uu____4524  ->
                                 let _0_429 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   _0_429);
                            norm cfg env'
                              ((Abs
                                  (env, bs, env', lopt,
                                    (t.FStar_Syntax_Syntax.pos))) :: stack)
                              body)))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let stack =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____4558  ->
                         fun stack  ->
                           match uu____4558 with
                           | (a,aq) ->
                               let _0_432 =
                                 Arg
                                   (let _0_431 =
                                      Clos
                                        (let _0_430 = FStar_Util.mk_ref None
                                            in
                                         (env, a, _0_430, false))
                                       in
                                    (_0_431, aq, (t.FStar_Syntax_Syntax.pos)))
                                  in
                               _0_432 :: stack) args)
                  in
               (log cfg
                  (fun uu____4581  ->
                     let _0_433 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" _0_433);
                norm cfg env stack head)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___154_4602 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___154_4602.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___154_4602.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t
                  | uu____4603 ->
                      let _0_434 = closure_as_term cfg env t  in
                      rebuild cfg env stack _0_434)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____4608 = FStar_Syntax_Subst.open_term [(x, None)] f
                     in
                  match uu____4608 with
                  | (closing,f) ->
                      let f = norm cfg (Dummy :: env) [] f  in
                      let t =
                        let _0_436 =
                          FStar_Syntax_Syntax.Tm_refine
                            (let _0_435 = FStar_Syntax_Subst.close closing f
                                in
                             ((let uu___155_4624 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_4624.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_4624.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), _0_435))
                           in
                        mk _0_436 t.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let _0_437 = closure_as_term cfg env t  in
                 rebuild cfg env stack _0_437
               else
                 (let uu____4638 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____4638 with
                  | (bs,c) ->
                      let c =
                        let _0_438 =
                          FStar_All.pipe_right bs
                            (FStar_List.fold_left
                               (fun env  -> fun uu____4649  -> Dummy :: env)
                               env)
                           in
                        norm_comp cfg _0_438 c  in
                      let t =
                        let _0_439 = norm_binders cfg env bs  in
                        FStar_Syntax_Util.arrow _0_439 c  in
                      rebuild cfg env stack t)
           | FStar_Syntax_Syntax.Tm_ascribed (t1,tc,l) ->
               (match stack with
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
                    _)::_ -> norm cfg env stack t1
                | uu____4691 ->
                    let t1 = norm cfg env [] t1  in
                    (log cfg
                       (fun uu____4694  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc =
                        match tc with
                        | FStar_Util.Inl t ->
                            FStar_Util.Inl (norm cfg env [] t)
                        | FStar_Util.Inr c ->
                            FStar_Util.Inr (norm_comp cfg env c)
                         in
                      let _0_440 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l))
                          t.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack _0_440)))
           | FStar_Syntax_Syntax.Tm_match (head,branches) ->
               let stack =
                 (Match (env, branches, (t.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack head
           | FStar_Syntax_Syntax.Tm_let
               ((uu____4758,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____4759;
                              FStar_Syntax_Syntax.lbunivs = uu____4760;
                              FStar_Syntax_Syntax.lbtyp = uu____4761;
                              FStar_Syntax_Syntax.lbeff = uu____4762;
                              FStar_Syntax_Syntax.lbdef = uu____4763;_}::uu____4764),uu____4765)
               -> rebuild cfg env stack t
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____4791 =
                 (Prims.op_Negation
                    (FStar_All.pipe_right cfg.steps
                       (FStar_List.contains NoDeltaSteps)))
                   &&
                   ((FStar_Syntax_Util.is_pure_effect n) ||
                      ((FStar_Syntax_Util.is_ghost_effect n) &&
                         (Prims.op_Negation
                            (FStar_All.pipe_right cfg.steps
                               (FStar_List.contains
                                  PureSubtermsWithinComputations)))))
                  in
               if uu____4791
               then
                 let env =
                   let _0_442 =
                     Clos
                       (let _0_441 = FStar_Util.mk_ref None  in
                        (env, (lb.FStar_Syntax_Syntax.lbdef), _0_441, false))
                      in
                   _0_442 :: env  in
                 norm cfg env stack body
               else
                 (let uu____4811 =
                    let _0_445 =
                      let _0_444 =
                        let _0_443 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left
                           in
                        FStar_All.pipe_right _0_443
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [_0_444]  in
                    FStar_Syntax_Subst.open_term _0_445 body  in
                  match uu____4811 with
                  | (bs,body) ->
                      let lb =
                        let uu___156_4819 = lb  in
                        let _0_451 =
                          let _0_448 =
                            let _0_446 = FStar_List.hd bs  in
                            FStar_All.pipe_right _0_446 Prims.fst  in
                          FStar_All.pipe_right _0_448
                            (fun _0_447  -> FStar_Util.Inl _0_447)
                           in
                        let _0_450 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                        let _0_449 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                        {
                          FStar_Syntax_Syntax.lbname = _0_451;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___156_4819.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = _0_450;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___156_4819.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = _0_449
                        }  in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env  -> fun uu____4833  -> Dummy :: env)
                             env)
                         in
                      norm cfg env'
                        ((Let (env, bs, lb, (t.FStar_Syntax_Syntax.pos))) ::
                        stack) body)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let _0_452 = closure_as_term cfg env t  in
               rebuild cfg env stack _0_452
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____4861 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____4883  ->
                        match uu____4883 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              FStar_Syntax_Syntax.bv_to_tm
                                (let uu___157_4922 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___157_4922.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___157_4922.FStar_Syntax_Syntax.sort)
                                 })
                               in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t.FStar_Syntax_Syntax.pos
                               in
                            let memo = FStar_Util.mk_ref None  in
                            let rec_env = (Clos (env, fix_f_i, memo, true))
                              :: rec_env  in
                            (rec_env, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____4861 with
                | (rec_env,memos,uu____4982) ->
                    let uu____4997 =
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
                           fun env  ->
                             let _0_454 =
                               Clos
                                 (let _0_453 = FStar_Util.mk_ref None  in
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                    _0_453, false))
                                in
                             _0_454 :: env) (Prims.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
                    let should_reify =
                      match stack with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____5070;
                             FStar_Syntax_Syntax.pos = uu____5071;
                             FStar_Syntax_Syntax.vars = uu____5072;_},uu____5073,uu____5074))::uu____5075
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5081 -> false  in
                    if Prims.op_Negation should_reify
                    then
                      let t = norm cfg env [] t  in
                      let stack = (Steps ((cfg.steps), (cfg.delta_level))) ::
                        stack  in
                      let cfg =
                        let uu____5087 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations)
                           in
                        if uu____5087
                        then
                          let uu___158_5088 = cfg  in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta];
                            tcenv = (uu___158_5088.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only]
                          }
                        else
                          (let uu___159_5090 = cfg  in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___159_5090.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta]
                           })
                         in
                      norm cfg env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m, t)),
                              (t.FStar_Syntax_Syntax.pos))) :: stack) head
                    else
                      (let uu____5092 =
                         (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                          in
                       match uu____5092 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m
                              in
                           let uu____5104 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____5104 with
                            | (uu____5105,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____5109 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____5116 =
                                         (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
                                          in
                                       match uu____5116 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____5119,uu____5120))
                                           ->
                                           let uu____5129 =
                                             (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
                                              in
                                           (match uu____5129 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____5132,msrc,uu____5134))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                Some
                                                  (FStar_Syntax_Subst.compress
                                                     e)
                                            | uu____5143 -> None)
                                       | uu____5144 -> None  in
                                     let uu____5145 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____5145 with
                                      | Some e ->
                                          let lb =
                                            let uu___160_5149 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___160_5149.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___160_5149.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___160_5149.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            }  in
                                          let _0_457 = FStar_List.tl stack
                                             in
                                          let _0_456 =
                                            (FStar_Syntax_Syntax.mk
                                               (FStar_Syntax_Syntax.Tm_let
                                                  (let _0_455 =
                                                     FStar_Syntax_Util.mk_reify
                                                       body
                                                      in
                                                   ((false, [lb]), _0_455))))
                                              None
                                              head.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env _0_457 _0_456
                                      | None  ->
                                          let uu____5168 =
                                            let uu____5169 = is_return body
                                               in
                                            match uu____5169 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____5172;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____5173;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____5174;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____5179 -> false  in
                                          if uu____5168
                                          then
                                            norm cfg env stack
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let head =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef
                                                in
                                             let body =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             let body =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_abs
                                                     (let _0_459 =
                                                        let _0_458 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            x
                                                           in
                                                        [_0_458]  in
                                                      (_0_459, body,
                                                        (Some
                                                           (FStar_Util.Inr
                                                              (m, [])))))))
                                                 None
                                                 body.FStar_Syntax_Syntax.pos
                                                in
                                             let bind_inst =
                                               let uu____5228 =
                                                 (FStar_Syntax_Subst.compress
                                                    bind_repr).FStar_Syntax_Syntax.n
                                                  in
                                               match uu____5228 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind,uu____5232::uu____5233::[])
                                                   ->
                                                   (FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_uinst
                                                         (let _0_463 =
                                                            let _0_462 =
                                                              (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                cfg.tcenv
                                                                lb.FStar_Syntax_Syntax.lbtyp
                                                               in
                                                            let _0_461 =
                                                              let _0_460 =
                                                                (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                  cfg.tcenv t
                                                                 in
                                                              [_0_460]  in
                                                            _0_462 :: _0_461
                                                             in
                                                          (bind, _0_463))))
                                                     None
                                                     t.FStar_Syntax_Syntax.pos
                                               | uu____5250 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects"
                                                in
                                             let reified =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_app
                                                     (let _0_475 =
                                                        let _0_474 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        let _0_473 =
                                                          let _0_472 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t
                                                             in
                                                          let _0_471 =
                                                            let _0_470 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let _0_469 =
                                                              let _0_468 =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head
                                                                 in
                                                              let _0_467 =
                                                                let _0_466 =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let _0_465 =
                                                                  let _0_464
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body  in
                                                                  [_0_464]
                                                                   in
                                                                _0_466 ::
                                                                  _0_465
                                                                 in
                                                              _0_468 ::
                                                                _0_467
                                                               in
                                                            _0_470 :: _0_469
                                                             in
                                                          _0_472 :: _0_471
                                                           in
                                                        _0_474 :: _0_473  in
                                                      (bind_inst, _0_475))))
                                                 None
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             let _0_476 = FStar_List.tl stack
                                                in
                                             norm cfg env _0_476 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m
                              in
                           let uu____5284 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____5284 with
                            | (uu____5285,bind_repr) ->
                                let maybe_unfold_action head =
                                  let maybe_extract_fv t =
                                    let t =
                                      let uu____5308 =
                                        (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                         in
                                      match uu____5308 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t,uu____5312) -> t
                                      | uu____5317 -> head  in
                                    let uu____5318 =
                                      (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                       in
                                    match uu____5318 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____5321 -> None  in
                                  let uu____5322 = maybe_extract_fv head  in
                                  match uu____5322 with
                                  | Some x when
                                      let _0_477 =
                                        FStar_Syntax_Syntax.lid_of_fv x  in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv _0_477
                                      ->
                                      let head = norm cfg env [] head  in
                                      let action_unfolded =
                                        let uu____5331 =
                                          maybe_extract_fv head  in
                                        match uu____5331 with
                                        | Some uu____5334 -> Some true
                                        | uu____5335 -> Some false  in
                                      (head, action_unfolded)
                                  | uu____5338 -> (head, None)  in
                                ((let is_arg_impure uu____5349 =
                                    match uu____5349 with
                                    | (e,q) ->
                                        let uu____5354 =
                                          (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
                                           in
                                        (match uu____5354 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m1,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m1)
                                         | uu____5367 -> false)
                                     in
                                  let uu____5368 =
                                    let _0_479 =
                                      let _0_478 =
                                        FStar_Syntax_Syntax.as_arg head_app
                                         in
                                      _0_478 :: args  in
                                    FStar_Util.for_some is_arg_impure _0_479
                                     in
                                  if uu____5368
                                  then
                                    failwith
                                      (let _0_480 =
                                         FStar_Syntax_Print.term_to_string
                                           head
                                          in
                                       FStar_Util.format1
                                         "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                         _0_480)
                                  else ());
                                 (let uu____5372 =
                                    maybe_unfold_action head_app  in
                                  match uu____5372 with
                                  | (head_app,found_action) ->
                                      let mk tm =
                                        FStar_Syntax_Syntax.mk tm None
                                          t.FStar_Syntax_Syntax.pos
                                         in
                                      let body =
                                        mk
                                          (FStar_Syntax_Syntax.Tm_app
                                             (head_app, args))
                                         in
                                      let body =
                                        match found_action with
                                        | None  ->
                                            FStar_Syntax_Util.mk_reify body
                                        | Some (false ) ->
                                            mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (body,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      (m, t))))
                                        | Some (true ) -> body  in
                                      let _0_481 = FStar_List.tl stack  in
                                      norm cfg env _0_481 body)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted = reify_lift cfg.tcenv e msrc mtgt t'
                              in
                           let _0_482 = FStar_List.tl stack  in
                           norm cfg env _0_482 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____5502  ->
                                     match uu____5502 with
                                     | (pat,wopt,tm) ->
                                         let _0_483 =
                                           FStar_Syntax_Util.mk_reify tm  in
                                         (pat, wopt, _0_483)))
                              in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches))
                               t.FStar_Syntax_Syntax.pos
                              in
                           let _0_484 = FStar_List.tl stack  in
                           norm cfg env _0_484 tm
                       | uu____5563 -> norm cfg env stack head)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
                    let should_reify =
                      match stack with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____5572;
                             FStar_Syntax_Syntax.pos = uu____5573;
                             FStar_Syntax_Syntax.vars = uu____5574;_},uu____5575,uu____5576))::uu____5577
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5583 -> false  in
                    if should_reify
                    then
                      let _0_486 = FStar_List.tl stack  in
                      let _0_485 = reify_lift cfg.tcenv head m m' t  in
                      norm cfg env _0_486 _0_485
                    else
                      (let uu____5585 =
                         ((FStar_Syntax_Util.is_pure_effect m) ||
                            (FStar_Syntax_Util.is_ghost_effect m))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations))
                          in
                       if uu____5585
                       then
                         let stack = (Steps ((cfg.steps), (cfg.delta_level)))
                           :: stack  in
                         let cfg =
                           let uu___161_5590 = cfg  in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___161_5590.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only]
                           }  in
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m, m', t)),
                                 (head.FStar_Syntax_Syntax.pos))) :: stack)
                           head
                       else
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic_lift
                                   (m, m', t)),
                                 (head.FStar_Syntax_Syntax.pos))) :: stack)
                           head)
                | uu____5596 ->
                    (match stack with
                     | uu____5597::uu____5598 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____5602)
                              -> norm cfg env ((Meta (m, r)) :: stack) head
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args = norm_pattern_args cfg env args  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args),
                                      (t.FStar_Syntax_Syntax.pos))) :: stack)
                                head
                          | uu____5617 -> norm cfg env stack head)
                     | uu____5618 ->
                         let head = norm cfg env [] head  in
                         let m =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               FStar_Syntax_Syntax.Meta_pattern
                                 (norm_pattern_args cfg env args)
                           | uu____5628 -> m  in
                         let t =
                           mk (FStar_Syntax_Syntax.Tm_meta (head, m))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t)))

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
              let uu____5642 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____5642 with
              | (uu____5643,return_repr) ->
                  let return_inst =
                    let uu____5650 =
                      (FStar_Syntax_Subst.compress return_repr).FStar_Syntax_Syntax.n
                       in
                    match uu____5650 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____5654::[])
                        ->
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_uinst
                              (let _0_488 =
                                 let _0_487 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [_0_487]  in
                               (return_tm, _0_488)))) None
                          e.FStar_Syntax_Syntax.pos
                    | uu____5671 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app
                        (let _0_492 =
                           let _0_491 = FStar_Syntax_Syntax.as_arg t  in
                           let _0_490 =
                             let _0_489 = FStar_Syntax_Syntax.as_arg e  in
                             [_0_489]  in
                           _0_491 :: _0_490  in
                         (return_inst, _0_492)))) None
                    e.FStar_Syntax_Syntax.pos
            else
              (let uu____5686 = FStar_TypeChecker_Env.monad_leq env msrc mtgt
                  in
               match uu____5686 with
               | None  ->
                   failwith
                     (FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        (FStar_Ident.text_of_lid msrc)
                        (FStar_Ident.text_of_lid mtgt))
               | Some
                   { FStar_TypeChecker_Env.msource = uu____5688;
                     FStar_TypeChecker_Env.mtarget = uu____5689;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____5690;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____5701;
                     FStar_TypeChecker_Env.mtarget = uu____5702;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____5703;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let _0_493 = FStar_Syntax_Util.mk_reify e  in
                   lift t FStar_Syntax_Syntax.tun _0_493)

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
                (fun uu____5750  ->
                   match uu____5750 with
                   | (a,imp) ->
                       let _0_494 = norm cfg env [] a  in (_0_494, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp = ghost_to_pure_aux cfg env comp  in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___162_5771 = comp  in
            let _0_497 =
              FStar_Syntax_Syntax.Total
                (let _0_496 = norm cfg env [] t  in
                 let _0_495 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_496, _0_495))
               in
            {
              FStar_Syntax_Syntax.n = _0_497;
              FStar_Syntax_Syntax.tk = (uu___162_5771.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___162_5771.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___162_5771.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___163_5787 = comp  in
            let _0_500 =
              FStar_Syntax_Syntax.GTotal
                (let _0_499 = norm cfg env [] t  in
                 let _0_498 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_499, _0_498))
               in
            {
              FStar_Syntax_Syntax.n = _0_500;
              FStar_Syntax_Syntax.tk = (uu___163_5787.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___163_5787.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___163_5787.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5819  ->
                      match uu____5819 with
                      | (a,i) ->
                          let _0_501 = norm cfg env [] a  in (_0_501, i)))
               in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___131_5830  ->
                      match uu___131_5830 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          FStar_Syntax_Syntax.DECREASES (norm cfg env [] t)
                      | f -> f))
               in
            let uu___164_5835 = comp  in
            let _0_505 =
              FStar_Syntax_Syntax.Comp
                (let uu___165_5838 = ct  in
                 let _0_504 =
                   FStar_List.map (norm_universe cfg env)
                     ct.FStar_Syntax_Syntax.comp_univs
                    in
                 let _0_503 =
                   norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                 let _0_502 = norm_args ct.FStar_Syntax_Syntax.effect_args
                    in
                 {
                   FStar_Syntax_Syntax.comp_univs = _0_504;
                   FStar_Syntax_Syntax.effect_name =
                     (uu___165_5838.FStar_Syntax_Syntax.effect_name);
                   FStar_Syntax_Syntax.result_typ = _0_503;
                   FStar_Syntax_Syntax.effect_args = _0_502;
                   FStar_Syntax_Syntax.flags = flags
                 })
               in
            {
              FStar_Syntax_Syntax.n = _0_505;
              FStar_Syntax_Syntax.tk = (uu___164_5835.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___164_5835.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___164_5835.FStar_Syntax_Syntax.vars)
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
        let norm t =
          norm
            (let uu___166_5850 = cfg  in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___166_5850.tcenv);
               delta_level = (uu___166_5850.delta_level)
             }) env [] t
           in
        let non_info t = FStar_Syntax_Util.non_informative (norm t)  in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____5857 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___167_5871 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___167_5871.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___167_5871.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_5871.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name
               in
            let uu____5881 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ)
               in
            if uu____5881
            then
              let ct =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___168_5886 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___168_5886.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___168_5886.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___168_5886.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___168_5886.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                       in
                    let uu___169_5888 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___169_5888.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___169_5888.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___169_5888.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___169_5888.FStar_Syntax_Syntax.flags)
                    }
                 in
              let uu___170_5889 = c  in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct);
                FStar_Syntax_Syntax.tk =
                  (uu___170_5889.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___170_5889.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___170_5889.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____5895 -> c

and norm_binder :
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____5898  ->
        match uu____5898 with
        | (x,imp) ->
            let _0_507 =
              let uu___171_5901 = x  in
              let _0_506 = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___171_5901.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___171_5901.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_506
              }  in
            (_0_507, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____5905 =
          FStar_List.fold_left
            (fun uu____5912  ->
               fun b  ->
                 match uu____5912 with
                 | (nbs',env) ->
                     let b = norm_binder cfg env b  in
                     ((b :: nbs'), (Dummy :: env))) ([], env) bs
           in
        match uu____5905 with | (nbs,uu____5929) -> FStar_List.rev nbs

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
            let uu____5946 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
            if uu____5946
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ  in
              let uu____5951 = FStar_Syntax_Util.is_total_lcomp lc  in
              (if uu____5951
               then
                 Some
                   (FStar_Util.Inl
                      (FStar_Syntax_Util.lcomp_of_comp
                         (let _0_508 = FStar_Syntax_Syntax.mk_Total t  in
                          FStar_Syntax_Util.comp_set_flags _0_508 flags)))
               else
                 Some
                   (FStar_Util.Inl
                      (FStar_Syntax_Util.lcomp_of_comp
                         (let _0_509 = FStar_Syntax_Syntax.mk_GTotal t  in
                          FStar_Syntax_Util.comp_set_flags _0_509 flags))))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____5970 -> lopt

and rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          match stack with
          | [] -> t
          | (Debug tm)::stack ->
              ((let uu____5982 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms")
                   in
                if uu____5982
                then
                  let _0_511 = FStar_Syntax_Print.term_to_string tm  in
                  let _0_510 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2 "Normalized %s to %s\n" _0_511 _0_510
                else ());
               rebuild cfg env stack t)
          | (Steps (s,dl))::stack ->
              rebuild
                (let uu___172_5990 = cfg  in
                 { steps = s; tcenv = (uu___172_5990.tcenv); delta_level = dl
                 }) env stack t
          | (Meta (m,r))::stack ->
              let t = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack t
          | (MemoLazy r)::stack ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____6010  ->
                    let _0_512 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" _0_512);
               rebuild cfg env stack t)
          | (Let (env',bs,lb,r))::stack ->
              let body = FStar_Syntax_Subst.close bs t  in
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) None r
                 in
              rebuild cfg env' stack t
          | (Abs (env',bs,env'',lopt,r))::stack ->
              let bs = norm_binders cfg env' bs  in
              let lopt = norm_lcomp_opt cfg env'' lopt  in
              let _0_513 =
                let uu___173_6047 = FStar_Syntax_Util.abs bs t lopt  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___173_6047.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___173_6047.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___173_6047.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack _0_513
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack ->
              let t = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack t
          | (Arg (Clos (env,tm,m,uu____6069),aq,r))::stack ->
              (log cfg
                 (fun uu____6085  ->
                    let _0_514 = FStar_Syntax_Print.term_to_string tm  in
                    FStar_Util.print1 "Rebuilding with arg %s\n" _0_514);
               if FStar_List.contains (Exclude Iota) cfg.steps
               then
                 (if FStar_List.contains WHNF cfg.steps
                  then
                    let arg = closure_as_term cfg env tm  in
                    let t = FStar_Syntax_Syntax.extend_app t (arg, aq) None r
                       in
                    rebuild cfg env stack t
                  else
                    (let stack = (App (t, aq, r)) :: stack  in
                     norm cfg env stack tm))
               else
                 (let uu____6096 = FStar_ST.read m  in
                  match uu____6096 with
                  | None  ->
                      if FStar_List.contains WHNF cfg.steps
                      then
                        let arg = closure_as_term cfg env tm  in
                        let t =
                          FStar_Syntax_Syntax.extend_app t (arg, aq) None r
                           in
                        rebuild cfg env stack t
                      else
                        (let stack = (MemoLazy m) :: (App (t, aq, r)) ::
                           stack  in
                         norm cfg env stack tm)
                  | Some (uu____6122,a) ->
                      let t = FStar_Syntax_Syntax.extend_app t (a, aq) None r
                         in
                      rebuild cfg env stack t))
          | (App (head,aq,r))::stack ->
              let t = FStar_Syntax_Syntax.extend_app head (t, aq) None r  in
              let _0_515 = maybe_simplify cfg.steps t  in
              rebuild cfg env stack _0_515
          | (Match (env,branches,r))::stack ->
              (log cfg
                 (fun uu____6150  ->
                    let _0_516 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n" _0_516);
               (let scrutinee = t  in
                let norm_and_rebuild_match uu____6155 =
                  let whnf = FStar_List.contains WHNF cfg.steps  in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___132_6162  ->
                              match uu___132_6162 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____6163 -> false))
                       in
                    let steps' =
                      let uu____6166 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations)
                         in
                      if uu____6166
                      then [Exclude Zeta]
                      else [Exclude Iota; Exclude Zeta]  in
                    let uu___174_6169 = cfg  in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___174_6169.tcenv);
                      delta_level = new_delta
                    }  in
                  let norm_or_whnf env t =
                    if whnf
                    then closure_as_term cfg_exclude_iota_zeta env t
                    else norm cfg_exclude_iota_zeta env [] t  in
                  let rec norm_pat env p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____6203 -> (p, env)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                        let uu____6223 = norm_pat env hd  in
                        (match uu____6223 with
                         | (hd,env') ->
                             let tl =
                               FStar_All.pipe_right tl
                                 (FStar_List.map
                                    (fun p  -> Prims.fst (norm_pat env p)))
                                in
                             ((let uu___175_6265 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd :: tl));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___175_6265.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___175_6265.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____6282 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____6316  ->
                                  fun uu____6317  ->
                                    match (uu____6316, uu____6317) with
                                    | ((pats,env),(p,b)) ->
                                        let uu____6382 = norm_pat env p  in
                                        (match uu____6382 with
                                         | (p,env) -> (((p, b) :: pats), env)))
                               ([], env))
                           in
                        (match uu____6282 with
                         | (pats,env) ->
                             ((let uu___176_6448 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___176_6448.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___176_6448.FStar_Syntax_Syntax.p)
                               }), env))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x =
                          let uu___177_6462 = x  in
                          let _0_517 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___177_6462.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___177_6462.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_517
                          }  in
                        ((let uu___178_6466 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x);
                            FStar_Syntax_Syntax.ty =
                              (uu___178_6466.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___178_6466.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x =
                          let uu___179_6471 = x  in
                          let _0_518 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___179_6471.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___179_6471.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_518
                          }  in
                        ((let uu___180_6475 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x);
                            FStar_Syntax_Syntax.ty =
                              (uu___180_6475.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___180_6475.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                        let x =
                          let uu___181_6485 = x  in
                          let _0_519 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___181_6485.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___181_6485.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_519
                          }  in
                        let t = norm_or_whnf env t  in
                        ((let uu___182_6490 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                            FStar_Syntax_Syntax.ty =
                              (uu___182_6490.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___182_6490.FStar_Syntax_Syntax.p)
                          }), env)
                     in
                  let branches =
                    match env with
                    | [] when whnf -> branches
                    | uu____6494 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch  ->
                                let uu____6497 =
                                  FStar_Syntax_Subst.open_branch branch  in
                                match uu____6497 with
                                | (p,wopt,e) ->
                                    let uu____6515 = norm_pat env p  in
                                    (match uu____6515 with
                                     | (p,env) ->
                                         let wopt =
                                           match wopt with
                                           | None  -> None
                                           | Some w ->
                                               Some (norm_or_whnf env w)
                                            in
                                         let e = norm_or_whnf env e  in
                                         FStar_Syntax_Util.branch
                                           (p, wopt, e))))
                     in
                  let _0_520 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches)) r
                     in
                  rebuild cfg env stack _0_520  in
                let rec is_cons head =
                  match head.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____6552) -> is_cons h
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
                  | uu____6563 -> false  in
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
                let rec matches_pat scrutinee p =
                  let scrutinee = FStar_Syntax_Util.unmeta scrutinee  in
                  let uu____6662 = FStar_Syntax_Util.head_and_args scrutinee
                     in
                  match uu____6662 with
                  | (head,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p  ->
                                  let m = matches_pat scrutinee p  in
                                  match m with
                                  | FStar_Util.Inl uu____6719 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None)
                              in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____6750 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____6762 ->
                                FStar_Util.Inr
                                  (Prims.op_Negation (is_cons head)))
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____6776 =
                             (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                              in
                           (match uu____6776 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____6781 ->
                                FStar_Util.Inr
                                  (Prims.op_Negation (is_cons head))))
                
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____6815)::rest_a,(p,uu____6818)::rest_p) ->
                      let uu____6846 = matches_pat t p  in
                      (match uu____6846 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____6860 -> FStar_Util.Inr false
                 in
                let rec matches scrutinee p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p,wopt,b)::rest ->
                      let uu____6931 = matches_pat scrutinee p  in
                      (match uu____6931 with
                       | FStar_Util.Inr (false ) -> matches scrutinee rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____6941  ->
                                 let _0_523 =
                                   FStar_Syntax_Print.pat_to_string p  in
                                 let _0_522 =
                                   let _0_521 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s
                                      in
                                   FStar_All.pipe_right _0_521
                                     (FStar_String.concat "; ")
                                    in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   _0_523 _0_522);
                            (let env =
                               FStar_List.fold_left
                                 (fun env  ->
                                    fun t  ->
                                      let _0_525 =
                                        Clos
                                          (let _0_524 =
                                             FStar_Util.mk_ref (Some ([], t))
                                              in
                                           ([], t, _0_524, false))
                                         in
                                      _0_525 :: env) env s
                                in
                             let _0_526 = guard_when_clause wopt b rest  in
                             norm cfg env stack _0_526)))
                   in
                let uu____6965 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota))
                   in
                if uu____6965
                then norm_and_rebuild_match ()
                else matches scrutinee branches))

let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___133_6979  ->
                match uu___133_6979 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____6982 -> []))
         in
      let d =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____6986 -> d  in
      { steps = s; tcenv = e; delta_level = d }
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  -> fun t  -> let _0_527 = config s e  in norm _0_527 [] [] t
  
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  -> fun t  -> let _0_528 = config s e  in norm_comp _0_528 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let _0_529 = config [] env  in norm_universe _0_529 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  -> let _0_530 = config [] env  in ghost_to_pure_aux _0_530 [] c
  
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
      let non_info t = FStar_Syntax_Util.non_informative (norm cfg [] [] t)
         in
      let uu____7029 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____7029
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___183_7031 = lc  in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___183_7031.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___183_7031.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____7032  ->
                    let _0_531 = lc.FStar_Syntax_Syntax.comp ()  in
                    ghost_to_pure env _0_531))
            }
        | None  -> lc
      else lc
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      FStar_Syntax_Print.term_to_string
        (normalize [AllowUnboundUniverses] env t)
  
let comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      FStar_Syntax_Print.comp_to_string
        (let _0_532 = config [AllowUnboundUniverses] env  in
         norm_comp _0_532 [] c)
  
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
        let rec aux t =
          let t = FStar_Syntax_Subst.compress t  in
          match t.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t0 = aux x.FStar_Syntax_Syntax.sort  in
              (match t0.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let _0_534 =
                     FStar_Syntax_Syntax.Tm_refine
                       (let _0_533 = FStar_Syntax_Util.mk_conj phi1 phi  in
                        (y, _0_533))
                      in
                   mk _0_534 t0.FStar_Syntax_Syntax.pos
               | uu____7084 -> t)
          | uu____7085 -> t  in
        aux t
  
let eta_expand_with_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun sort  ->
      let uu____7092 = FStar_Syntax_Util.arrow_formals_comp sort  in
      match uu____7092 with
      | (binders,c) ->
          (match binders with
           | [] -> t
           | uu____7108 ->
               let uu____7112 =
                 FStar_All.pipe_right binders
                   FStar_Syntax_Util.args_of_binders
                  in
               (match uu____7112 with
                | (binders,args) ->
                    let _0_539 =
                      (FStar_Syntax_Syntax.mk_Tm_app t args) None
                        t.FStar_Syntax_Syntax.pos
                       in
                    let _0_538 =
                      let _0_537 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.lcomp_of_comp c)
                          (fun _0_535  -> FStar_Util.Inl _0_535)
                         in
                      FStar_All.pipe_right _0_537
                        (fun _0_536  -> Some _0_536)
                       in
                    FStar_Syntax_Util.abs binders _0_539 _0_538))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____7158 =
        let _0_540 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
        (_0_540, (t.FStar_Syntax_Syntax.n))  in
      match uu____7158 with
      | (Some sort,uu____7167) ->
          let _0_541 = mk sort t.FStar_Syntax_Syntax.pos  in
          eta_expand_with_type t _0_541
      | (uu____7169,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type t x.FStar_Syntax_Syntax.sort
      | uu____7173 ->
          let uu____7177 = FStar_Syntax_Util.head_and_args t  in
          (match uu____7177 with
           | (head,args) ->
               let uu____7203 =
                 (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n  in
               (match uu____7203 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____7204,thead) ->
                    let uu____7218 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____7218 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____7249 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___184_7253 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___184_7253.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___184_7253.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___184_7253.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___184_7253.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___184_7253.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___184_7253.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___184_7253.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___184_7253.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___184_7253.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___184_7253.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___184_7253.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___184_7253.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___184_7253.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___184_7253.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___184_7253.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___184_7253.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___184_7253.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___184_7253.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___184_7253.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___184_7253.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___184_7253.FStar_TypeChecker_Env.qname_and_index)
                                 }) t
                               in
                            match uu____7249 with
                            | (uu____7254,ty,uu____7256) ->
                                eta_expand_with_type t ty))
                | uu____7257 ->
                    let uu____7258 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___185_7262 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___185_7262.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___185_7262.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___185_7262.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___185_7262.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___185_7262.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___185_7262.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___185_7262.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___185_7262.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___185_7262.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___185_7262.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___185_7262.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___185_7262.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___185_7262.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___185_7262.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___185_7262.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___185_7262.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___185_7262.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___185_7262.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___185_7262.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___185_7262.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___185_7262.FStar_TypeChecker_Env.qname_and_index)
                         }) t
                       in
                    (match uu____7258 with
                     | (uu____7263,ty,uu____7265) ->
                         eta_expand_with_type t ty)))
  