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
    let _0_305 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right _0_305 (FStar_String.concat "; ")
  
let stack_elt_to_string : stack_elt -> Prims.string =
  fun uu___128_591  ->
    match uu___128_591 with
    | Arg (c,uu____593,uu____594) ->
        let _0_306 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" _0_306
    | MemoLazy uu____595 -> "MemoLazy"
    | Abs (uu____599,bs,uu____601,uu____602,uu____603) ->
        let _0_307 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" _0_307
    | UnivArgs uu____614 -> "UnivArgs"
    | Match uu____618 -> "Match"
    | App (t,uu____623,uu____624) ->
        let _0_308 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" _0_308
    | Meta (m,uu____626) -> "Meta"
    | Let uu____627 -> "Let"
    | Steps (s,uu____633) -> "Steps"
    | Debug t ->
        let _0_309 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" _0_309
  
let stack_to_string : stack_elt Prims.list -> Prims.string =
  fun s  ->
    let _0_310 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right _0_310 (FStar_String.concat "; ")
  
let log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____654 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____654 then f () else ()
  
let is_empty uu___129_663 =
  match uu___129_663 with | [] -> true | uu____665 -> false 
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____683 ->
      failwith
        (let _0_311 = FStar_Syntax_Print.db_to_string x  in
         FStar_Util.format1 "Failed to find %s\n" _0_311)
  
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
                let _0_312 = FStar_List.collect aux us  in
                FStar_All.pipe_right _0_312 norm_univs  in
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
              let _0_314 = aux u  in
              FStar_List.map
                (fun _0_313  -> FStar_Syntax_Syntax.U_succ _0_313) _0_314
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
             let _0_316 = FStar_Syntax_Print.tag_of_term t  in
             let _0_315 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" _0_316 _0_315);
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
                  let _0_317 =
                    FStar_Syntax_Syntax.Tm_type (norm_universe cfg env u)  in
                  mk _0_317 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
                  let _0_318 = FStar_List.map (norm_universe cfg env) us  in
                  FStar_Syntax_Syntax.mk_Tm_uinst t _0_318
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
                       let _0_320 =
                         FStar_Syntax_Syntax.Tm_abs
                           (let _0_319 = close_lcomp_opt cfg env lopt  in
                            (bs, body, _0_319))
                          in
                       mk _0_320 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1081 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1081 with
                   | (bs,env) ->
                       let c = close_comp cfg env c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                         t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1112 =
                    let _0_322 =
                      let _0_321 = FStar_Syntax_Syntax.mk_binder x  in
                      [_0_321]  in
                    closures_as_binders_delayed cfg env _0_322  in
                  (match uu____1112 with
                   | (x,env) ->
                       let phi = closure_as_term_delayed cfg env phi  in
                       let _0_325 =
                         FStar_Syntax_Syntax.Tm_refine
                           (let _0_324 =
                              let _0_323 = FStar_List.hd x  in
                              FStar_All.pipe_right _0_323 Prims.fst  in
                            (_0_324, phi))
                          in
                       mk _0_325 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,lopt)
                  ->
                  let _0_330 =
                    FStar_Syntax_Syntax.Tm_ascribed
                      (let _0_329 = closure_as_term_delayed cfg env t1  in
                       let _0_328 =
                         let _0_327 = closure_as_term_delayed cfg env t2  in
                         FStar_All.pipe_left
                           (fun _0_326  -> FStar_Util.Inl _0_326) _0_327
                          in
                       (_0_329, _0_328, lopt))
                     in
                  mk _0_330 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,lopt) ->
                  let _0_335 =
                    FStar_Syntax_Syntax.Tm_ascribed
                      (let _0_334 = closure_as_term_delayed cfg env t1  in
                       let _0_333 =
                         let _0_332 = close_comp cfg env c  in
                         FStar_All.pipe_left
                           (fun _0_331  -> FStar_Util.Inr _0_331) _0_332
                          in
                       (_0_334, _0_333, lopt))
                     in
                  mk _0_335 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let _0_338 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_337 = closure_as_term_delayed cfg env t'  in
                       let _0_336 =
                         FStar_Syntax_Syntax.Meta_pattern
                           (FStar_All.pipe_right args
                              (FStar_List.map
                                 (closures_as_args_delayed cfg env)))
                          in
                       (_0_337, _0_336))
                     in
                  mk _0_338 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let _0_342 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_341 = closure_as_term_delayed cfg env t'  in
                       let _0_340 =
                         FStar_Syntax_Syntax.Meta_monadic
                           (let _0_339 =
                              closure_as_term_delayed cfg env tbody  in
                            (m, _0_339))
                          in
                       (_0_341, _0_340))
                     in
                  mk _0_342 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let _0_346 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_345 = closure_as_term_delayed cfg env t'  in
                       let _0_344 =
                         FStar_Syntax_Syntax.Meta_monadic_lift
                           (let _0_343 =
                              closure_as_term_delayed cfg env tbody  in
                            (m1, m2, _0_343))
                          in
                       (_0_345, _0_344))
                     in
                  mk _0_346 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let _0_348 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_347 = closure_as_term_delayed cfg env t'  in
                       (_0_347, m))
                     in
                  mk _0_348 t.FStar_Syntax_Syntax.pos
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
                    let uu___141_1327 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___141_1327.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___141_1327.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___141_1327.FStar_Syntax_Syntax.lbeff);
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
                    let uu___142_1370 = lb  in
                    let _0_350 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let _0_349 =
                      closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___142_1370.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___142_1370.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = _0_350;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___142_1370.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = _0_349
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
                                   ((let uu___143_1542 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd ::
                                            tl));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___143_1542.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___143_1542.FStar_Syntax_Syntax.p)
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
                                   ((let uu___144_1725 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___144_1725.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___144_1725.FStar_Syntax_Syntax.p)
                                     }), env))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x =
                                let uu___145_1739 = x  in
                                let _0_351 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___145_1739.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___145_1739.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_351
                                }  in
                              ((let uu___146_1743 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___146_1743.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___146_1743.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x =
                                let uu___147_1748 = x  in
                                let _0_352 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___147_1748.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___147_1748.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_352
                                }  in
                              ((let uu___148_1752 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___148_1752.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___148_1752.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                              let x =
                                let uu___149_1762 = x  in
                                let _0_353 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___149_1762.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___149_1762.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_353
                                }  in
                              let t = closure_as_term cfg env t  in
                              ((let uu___150_1767 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___150_1767.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___150_1767.FStar_Syntax_Syntax.p)
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
                  let _0_355 =
                    FStar_Syntax_Syntax.Tm_match
                      (let _0_354 =
                         FStar_All.pipe_right branches
                           (FStar_List.map (norm_one_branch env))
                          in
                       (head, _0_354))
                     in
                  mk _0_355 t.FStar_Syntax_Syntax.pos))

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
                     let _0_356 = closure_as_term_delayed cfg env x  in
                     (_0_356, imp)) args

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
                          let uu___151_1962 = b  in
                          let _0_357 =
                            closure_as_term_delayed cfg env
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___151_1962.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___151_1962.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_357
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
                 let _0_359 = closure_as_term_delayed cfg env t  in
                 let _0_358 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 FStar_Syntax_Syntax.mk_Total' _0_359 _0_358
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let _0_361 = closure_as_term_delayed cfg env t  in
                 let _0_360 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 FStar_Syntax_Syntax.mk_GTotal' _0_361 _0_360
             | FStar_Syntax_Syntax.Comp c ->
                 let args =
                   closures_as_args_delayed cfg env
                     c.FStar_Syntax_Syntax.effect_args
                    in
                 let flags =
                   FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___130_2038  ->
                           match uu___130_2038 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               FStar_Syntax_Syntax.DECREASES
                                 (closure_as_term_delayed cfg env t)
                           | f -> f))
                    in
                 FStar_Syntax_Syntax.mk_Comp
                   (let uu___152_2043 = c  in
                    let _0_362 =
                      FStar_List.map (norm_universe cfg env)
                        c.FStar_Syntax_Syntax.comp_univs
                       in
                    {
                      FStar_Syntax_Syntax.comp_typ_name =
                        (uu___152_2043.FStar_Syntax_Syntax.comp_typ_name);
                      FStar_Syntax_Syntax.comp_univs = _0_362;
                      FStar_Syntax_Syntax.effect_args = args;
                      FStar_Syntax_Syntax.flags = flags
                    }))

and filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
      (FStar_List.filter
         (fun uu___131_2047  ->
            match uu___131_2047 with
            | FStar_Syntax_Syntax.DECREASES uu____2048 -> false
            | uu____2051 -> true))

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
            let uu____2079 = FStar_Syntax_Util.is_total_lcomp lc  in
            if uu____2079
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2096 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
               if uu____2096
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr
                      ((lc.FStar_Syntax_Syntax.lcomp_name), flags)))
        | uu____2122 -> lopt

let arith_ops :
  (FStar_Ident.lident * (Prims.int -> Prims.int -> FStar_Const.sconst))
    Prims.list
  =
  let int_as_const i =
    FStar_Const.Const_int
      (let _0_363 = FStar_Util.string_of_int i  in (_0_363, None))
     in
  let bool_as_const b = FStar_Const.Const_bool b  in
  let _0_372 =
    FStar_List.flatten
      (FStar_List.map
         (fun m  ->
            let _0_371 =
              let _0_364 = FStar_Syntax_Const.p2l ["FStar"; m; "add"]  in
              (_0_364, (fun x  -> fun y  -> int_as_const (x + y)))  in
            let _0_370 =
              let _0_369 =
                let _0_365 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"]  in
                (_0_365, (fun x  -> fun y  -> int_as_const (x - y)))  in
              let _0_368 =
                let _0_367 =
                  let _0_366 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"]  in
                  (_0_366, (fun x  -> fun y  -> int_as_const (x * y)))  in
                [_0_367]  in
              _0_369 :: _0_368  in
            _0_371 :: _0_370)
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
      ((fun x  -> fun y  -> int_as_const (x mod y))))] _0_372
  
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
         (let _0_373 = FStar_Syntax_Const.p2l x  in
          FStar_Syntax_Syntax.lid_as_fv _0_373
            FStar_Syntax_Syntax.Delta_constant None))
     in
  let ctor x =
    mk
      (FStar_Syntax_Syntax.Tm_fvar
         (let _0_374 = FStar_Syntax_Const.p2l x  in
          FStar_Syntax_Syntax.lid_as_fv _0_374
            FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor)))
     in
  let _0_391 =
    let _0_390 = FStar_Syntax_Const.p2l ["FStar"; "String"; "list_of_string"]
       in
    (_0_390,
      (fun s  ->
         let _0_389 = FStar_String.list_of_string s  in
         let _0_388 =
           mk
             (FStar_Syntax_Syntax.Tm_app
                (let _0_387 =
                   let _0_383 = ctor ["Prims"; "Nil"]  in
                   FStar_Syntax_Syntax.mk_Tm_uinst _0_383
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let _0_386 =
                   let _0_385 =
                     let _0_384 = name ["FStar"; "Char"; "char"]  in
                     (_0_384, (Some (FStar_Syntax_Syntax.Implicit true)))  in
                   [_0_385]  in
                 (_0_387, _0_386)))
            in
         FStar_List.fold_right
           (fun c  ->
              fun a  ->
                mk
                  (FStar_Syntax_Syntax.Tm_app
                     (let _0_382 =
                        let _0_375 = ctor ["Prims"; "Cons"]  in
                        FStar_Syntax_Syntax.mk_Tm_uinst _0_375
                          [FStar_Syntax_Syntax.U_zero]
                         in
                      let _0_381 =
                        let _0_380 =
                          let _0_376 = name ["FStar"; "Char"; "char"]  in
                          (_0_376,
                            (Some (FStar_Syntax_Syntax.Implicit true)))
                           in
                        let _0_379 =
                          let _0_378 =
                            let _0_377 =
                              mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_char c))
                               in
                            (_0_377, None)  in
                          [_0_378; (a, None)]  in
                        _0_380 :: _0_379  in
                      (_0_382, _0_381)))) _0_389 _0_388))
     in
  [_0_391] 
let reduce_equality :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let is_decidable_equality t =
      let uu____2461 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____2461 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq
      | uu____2463 -> false  in
    let is_propositional_equality t =
      let uu____2468 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____2468 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
      | uu____2470 -> false  in
    match tm.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app
        (op_eq_inst,(_typ,uu____2475)::(a1,uu____2477)::(a2,uu____2479)::[])
        when is_decidable_equality op_eq_inst ->
        let tt =
          let uu____2520 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2520 with
          | FStar_Syntax_Util.Equal  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool true)) tm.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Util.NotEqual  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool false)) tm.FStar_Syntax_Syntax.pos
          | uu____2523 -> tm  in
        tt
    | FStar_Syntax_Syntax.Tm_app (eq2_inst,_::(a1,_)::(a2,_)::[])
      |FStar_Syntax_Syntax.Tm_app (eq2_inst,(a1,_)::(a2,_)::[]) when
        is_propositional_equality eq2_inst ->
        let tt =
          let uu____2595 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2595 with
          | FStar_Syntax_Util.Equal  -> FStar_Syntax_Util.t_true
          | FStar_Syntax_Util.NotEqual  -> FStar_Syntax_Util.t_false
          | uu____2596 -> tm  in
        tt
    | uu____2597 -> tm
  
let find_fv fv ops =
  match fv.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_List.tryFind
        (fun uu____2622  ->
           match uu____2622 with
           | (l,uu____2626) -> FStar_Syntax_Syntax.fv_eq_lid fv l) ops
  | uu____2627 -> None 
let reduce_primops :
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let uu____2644 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops steps)
         in
      if uu____2644
      then tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             (fv,(a1,uu____2652)::(a2,uu____2654)::[]) ->
             let uu____2684 = find_fv fv arith_ops  in
             (match uu____2684 with
              | None  -> tm
              | Some (uu____2704,op) ->
                  let norm i j =
                    let c =
                      let _0_393 = FStar_Util.int_of_string i  in
                      let _0_392 = FStar_Util.int_of_string j  in
                      op _0_393 _0_392  in
                    mk (FStar_Syntax_Syntax.Tm_constant c)
                      tm.FStar_Syntax_Syntax.pos
                     in
                  let uu____2730 =
                    let _0_395 =
                      (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
                       in
                    let _0_394 =
                      (FStar_Syntax_Subst.compress a2).FStar_Syntax_Syntax.n
                       in
                    (_0_395, _0_394)  in
                  (match uu____2730 with
                   | (FStar_Syntax_Syntax.Tm_app
                      (head1,(arg1,uu____2737)::[]),FStar_Syntax_Syntax.Tm_app
                      (head2,(arg2,uu____2740)::[])) ->
                       let uu____2783 =
                         let _0_399 =
                           (FStar_Syntax_Subst.compress head1).FStar_Syntax_Syntax.n
                            in
                         let _0_398 =
                           (FStar_Syntax_Subst.compress head2).FStar_Syntax_Syntax.n
                            in
                         let _0_397 =
                           (FStar_Syntax_Subst.compress arg1).FStar_Syntax_Syntax.n
                            in
                         let _0_396 =
                           (FStar_Syntax_Subst.compress arg2).FStar_Syntax_Syntax.n
                            in
                         (_0_399, _0_398, _0_397, _0_396)  in
                       (match uu____2783 with
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
                            let _0_403 =
                              mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                                tm.FStar_Syntax_Syntax.pos
                               in
                            let _0_402 =
                              let _0_401 =
                                let _0_400 = norm i j  in (_0_400, None)  in
                              [_0_401]  in
                            FStar_Syntax_Util.mk_app _0_403 _0_402
                        | uu____2825 -> tm)
                   | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                      (i,None )),FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (j,None ))) -> norm i j
                   | uu____2842 -> tm))
         | FStar_Syntax_Syntax.Tm_app (fv,(a1,uu____2847)::[]) ->
             let uu____2869 = find_fv fv un_ops  in
             (match uu____2869 with
              | None  -> tm
              | Some (uu____2889,op) ->
                  let uu____2905 =
                    (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
                     in
                  (match uu____2905 with
                   | FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_string (b,uu____2909)) ->
                       op (FStar_Bytes.unicode_bytes_as_string b)
                   | uu____2912 -> tm))
         | uu____2913 -> reduce_equality tm)
  
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
        let uu___153_2938 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___153_2938.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___153_2938.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___153_2938.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____2957 -> None  in
      let simplify arg = ((simp_t (Prims.fst arg)), arg)  in
      let uu____2984 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps)
         in
      if uu____2984
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
             let uu____3028 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid
                in
             if uu____3028
             then
               let uu____3031 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               (match uu____3031 with
                | (Some (true ),_)::(_,(arg,_))::[]
                  |(_,(arg,_))::(Some (true ),_)::[] -> arg
                | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____3199 -> tm)
             else
               (let uu____3209 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid
                   in
                if uu____3209
                then
                  let uu____3212 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____3212 with
                  | (Some (true ),_)::_::[]|_::(Some (true ),_)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),_)::(_,(arg,_))::[]
                    |(_,(arg,_))::(Some (false ),_)::[] -> arg
                  | uu____3380 -> tm
                else
                  (let uu____3390 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid
                      in
                   if uu____3390
                   then
                     let uu____3393 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____3393 with
                     | _::(Some (true ),_)::[]|(Some (false ),_)::_::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____3484)::(uu____3485,(arg,uu____3487))::[]
                         -> arg
                     | uu____3528 -> tm
                   else
                     (let uu____3538 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid
                         in
                      if uu____3538
                      then
                        let uu____3541 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____3541 with
                        | (Some (true ),uu____3576)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____3600)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____3624 -> tm
                      else
                        (let uu____3634 =
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.forall_lid)
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid)
                            in
                         if uu____3634
                         then
                           match args with
                           | (t,_)::[]
                             |(_,Some (FStar_Syntax_Syntax.Implicit _))::
                             (t,_)::[] ->
                               let uu____3679 =
                                 (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                  in
                               (match uu____3679 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____3682::[],body,uu____3684) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | Some (false ) ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____3712 -> tm)
                                | uu____3714 -> tm)
                           | uu____3715 -> tm
                         else reduce_equality tm))))
         | uu____3722 -> tm)
  
let is_norm_request hd args =
  let uu____3737 =
    let _0_404 = (FStar_Syntax_Util.un_uinst hd).FStar_Syntax_Syntax.n  in
    (_0_404, args)  in
  match uu____3737 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3743::uu____3744::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3747::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____3749 -> false 
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____3782 -> failwith "Impossible" 
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t = FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____3878  ->
               let _0_407 = FStar_Syntax_Print.tag_of_term t  in
               let _0_406 = FStar_Syntax_Print.term_to_string t  in
               let _0_405 = stack_to_string stack  in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" _0_407 _0_406
                 _0_405);
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____3879 ->
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
                 let uu___154_3938 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___154_3938.tcenv);
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
                  FStar_Syntax_Syntax.tk = uu____3942;
                  FStar_Syntax_Syntax.pos = uu____3943;
                  FStar_Syntax_Syntax.vars = uu____3944;_},a1::a2::rest)
               ->
               let uu____3978 = FStar_Syntax_Util.head_and_args t  in
               (match uu____3978 with
                | (hd,uu____3989) ->
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
                  FStar_Syntax_Syntax.tk = uu____4044;
                  FStar_Syntax_Syntax.pos = uu____4045;
                  FStar_Syntax_Syntax.vars = uu____4046;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4069 = FStar_Syntax_Util.head_and_args t  in
               (match uu____4069 with
                | (reify_head,uu____4080) ->
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
                              (FStar_Const.Const_reflect uu____4098);
                            FStar_Syntax_Syntax.tk = uu____4099;
                            FStar_Syntax_Syntax.pos = uu____4100;
                            FStar_Syntax_Syntax.vars = uu____4101;_},a::[])
                         -> norm cfg env stack (Prims.fst a)
                     | uu____4126 ->
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
               let uu____4140 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____4140
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
                      (fun uu___132_4150  ->
                         match uu___132_4150 with
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
                  let uu____4154 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  match uu____4154 with
                  | None  ->
                      (log cfg
                         (fun uu____4165  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack t)
                  | Some (us,t) ->
                      (log cfg
                         (fun uu____4171  ->
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
                          | (UnivArgs (us',uu____4178))::stack ->
                              let env =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env  -> fun u  -> (Univ u) :: env)
                                     env)
                                 in
                              norm cfg env stack t
                          | uu____4191 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack t
                          | uu____4192 ->
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
               let uu____4199 = lookup_bvar env x  in
               (match uu____4199 with
                | Univ uu____4200 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____4215 = FStar_ST.read r  in
                      (match uu____4215 with
                       | Some (env,t') ->
                           (log cfg
                              (fun uu____4234  ->
                                 let _0_415 =
                                   FStar_Syntax_Print.term_to_string t  in
                                 let _0_414 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" _0_415
                                   _0_414);
                            (let uu____4235 =
                               (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
                                in
                             match uu____4235 with
                             | FStar_Syntax_Syntax.Tm_abs uu____4236 ->
                                 norm cfg env stack t'
                             | uu____4251 -> rebuild cfg env stack t'))
                       | None  -> norm cfg env ((MemoLazy r) :: stack) t0)
                    else norm cfg env stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____4284)::uu____4285 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4290)::uu____4291 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4297,uu____4298))::stack_rest ->
                    (match c with
                     | Univ uu____4301 -> norm cfg (c :: env) stack_rest t
                     | uu____4302 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____4305::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____4318  ->
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
                                           (fun uu___133_4332  ->
                                              match uu___133_4332 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____4333 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____4335  ->
                                         let _0_417 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_417);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____4346  ->
                                         let _0_418 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_418);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____4347 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____4354 ->
                                   let cfg =
                                     let uu___155_4362 = cfg  in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___155_4362.tcenv);
                                       delta_level =
                                         (uu___155_4362.delta_level)
                                     }  in
                                   let _0_419 = closure_as_term cfg env t  in
                                   rebuild cfg env stack _0_419)
                          | uu____4363::tl ->
                              (log cfg
                                 (fun uu____4373  ->
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
                      (let uu___156_4394 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___156_4394.tcenv);
                         delta_level = dl
                       }) env stack t
                | (MemoLazy r)::stack ->
                    (set_memo r (env, t);
                     log cfg
                       (fun uu____4407  ->
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
                      (let uu____4419 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____4419 with
                       | (bs,body,opening) ->
                           let lopt =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 Some
                                   (FStar_Util.Inl
                                      (let _0_424 =
                                         let _0_423 =
                                           l.FStar_Syntax_Syntax.lcomp_as_comp
                                             ()
                                            in
                                         FStar_Syntax_Subst.subst_comp
                                           opening _0_423
                                          in
                                       FStar_TypeChecker_Env.lcomp_of_comp
                                         cfg.tcenv _0_424))
                             | uu____4456 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun uu____4470  -> Dummy :: env) env)
                              in
                           (log cfg
                              (fun uu____4475  ->
                                 let _0_425 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   _0_425);
                            norm cfg env'
                              ((Abs
                                  (env, bs, env', lopt,
                                    (t.FStar_Syntax_Syntax.pos))) :: stack)
                              body)))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let stack =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____4509  ->
                         fun stack  ->
                           match uu____4509 with
                           | (a,aq) ->
                               let _0_428 =
                                 Arg
                                   (let _0_427 =
                                      Clos
                                        (let _0_426 = FStar_Util.mk_ref None
                                            in
                                         (env, a, _0_426, false))
                                       in
                                    (_0_427, aq, (t.FStar_Syntax_Syntax.pos)))
                                  in
                               _0_428 :: stack) args)
                  in
               (log cfg
                  (fun uu____4532  ->
                     let _0_429 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" _0_429);
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
                             ((let uu___157_4553 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_4553.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_4553.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t
                  | uu____4554 ->
                      let _0_430 = closure_as_term cfg env t  in
                      rebuild cfg env stack _0_430)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____4559 = FStar_Syntax_Subst.open_term [(x, None)] f
                     in
                  match uu____4559 with
                  | (closing,f) ->
                      let f = norm cfg (Dummy :: env) [] f  in
                      let t =
                        let _0_432 =
                          FStar_Syntax_Syntax.Tm_refine
                            (let _0_431 = FStar_Syntax_Subst.close closing f
                                in
                             ((let uu___158_4575 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___158_4575.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___158_4575.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), _0_431))
                           in
                        mk _0_432 t.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let _0_433 = closure_as_term cfg env t  in
                 rebuild cfg env stack _0_433
               else
                 (let uu____4589 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____4589 with
                  | (bs,c) ->
                      let c =
                        let _0_434 =
                          FStar_All.pipe_right bs
                            (FStar_List.fold_left
                               (fun env  -> fun uu____4600  -> Dummy :: env)
                               env)
                           in
                        norm_comp cfg _0_434 c  in
                      let t =
                        let _0_435 = norm_binders cfg env bs  in
                        FStar_Syntax_Util.arrow _0_435 c  in
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
                | uu____4640 ->
                    let t1 = norm cfg env [] t1  in
                    (log cfg
                       (fun uu____4643  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc =
                        match tc with
                        | FStar_Util.Inl t ->
                            FStar_Util.Inl (norm cfg env [] t)
                        | FStar_Util.Inr c ->
                            FStar_Util.Inr (norm_comp cfg env c)
                         in
                      let _0_436 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l))
                          t.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack _0_436)))
           | FStar_Syntax_Syntax.Tm_match (head,branches) ->
               let stack =
                 (Match (env, branches, (t.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack head
           | FStar_Syntax_Syntax.Tm_let
               ((uu____4707,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____4708;
                              FStar_Syntax_Syntax.lbunivs = uu____4709;
                              FStar_Syntax_Syntax.lbtyp = uu____4710;
                              FStar_Syntax_Syntax.lbeff = uu____4711;
                              FStar_Syntax_Syntax.lbdef = uu____4712;_}::uu____4713),uu____4714)
               -> rebuild cfg env stack t
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____4740 =
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
               if uu____4740
               then
                 let env =
                   let _0_438 =
                     Clos
                       (let _0_437 = FStar_Util.mk_ref None  in
                        (env, (lb.FStar_Syntax_Syntax.lbdef), _0_437, false))
                      in
                   _0_438 :: env  in
                 norm cfg env stack body
               else
                 (let uu____4760 =
                    let _0_441 =
                      let _0_440 =
                        let _0_439 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left
                           in
                        FStar_All.pipe_right _0_439
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [_0_440]  in
                    FStar_Syntax_Subst.open_term _0_441 body  in
                  match uu____4760 with
                  | (bs,body) ->
                      let lb =
                        let uu___159_4768 = lb  in
                        let _0_447 =
                          let _0_444 =
                            let _0_442 = FStar_List.hd bs  in
                            FStar_All.pipe_right _0_442 Prims.fst  in
                          FStar_All.pipe_right _0_444
                            (fun _0_443  -> FStar_Util.Inl _0_443)
                           in
                        let _0_446 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                        let _0_445 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                        {
                          FStar_Syntax_Syntax.lbname = _0_447;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___159_4768.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = _0_446;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___159_4768.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = _0_445
                        }  in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env  -> fun uu____4782  -> Dummy :: env)
                             env)
                         in
                      norm cfg env'
                        ((Let (env, bs, lb, (t.FStar_Syntax_Syntax.pos))) ::
                        stack) body)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let _0_448 = closure_as_term cfg env t  in
               rebuild cfg env stack _0_448
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____4810 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____4832  ->
                        match uu____4832 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              FStar_Syntax_Syntax.bv_to_tm
                                (let uu___160_4871 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___160_4871.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___160_4871.FStar_Syntax_Syntax.sort)
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
               (match uu____4810 with
                | (rec_env,memos,uu____4931) ->
                    let uu____4946 =
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
                             let _0_450 =
                               Clos
                                 (let _0_449 = FStar_Util.mk_ref None  in
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                    _0_449, false))
                                in
                             _0_450 :: env) (Prims.snd lbs) env
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
                             FStar_Syntax_Syntax.tk = uu____5019;
                             FStar_Syntax_Syntax.pos = uu____5020;
                             FStar_Syntax_Syntax.vars = uu____5021;_},uu____5022,uu____5023))::uu____5024
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5030 -> false  in
                    if Prims.op_Negation should_reify
                    then
                      let t = norm cfg env [] t  in
                      let stack = (Steps ((cfg.steps), (cfg.delta_level))) ::
                        stack  in
                      let cfg =
                        let uu___161_5036 = cfg  in
                        {
                          steps =
                            (FStar_List.append [NoDeltaSteps; Exclude Zeta]
                               cfg.steps);
                          tcenv = (uu___161_5036.tcenv);
                          delta_level = [FStar_TypeChecker_Env.NoDelta]
                        }  in
                      norm cfg env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m, t)),
                              (t.FStar_Syntax_Syntax.pos))) :: stack) head
                    else
                      (let uu____5038 =
                         (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                          in
                       match uu____5038 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m
                              in
                           let uu____5050 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____5050 with
                            | (uu____5051,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inl x ->
                                     let head =
                                       FStar_All.pipe_left
                                         FStar_Syntax_Util.mk_reify
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     let body =
                                       FStar_All.pipe_left
                                         FStar_Syntax_Util.mk_reify body
                                        in
                                     let body =
                                       (FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_abs
                                             (let _0_452 =
                                                let _0_451 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x
                                                   in
                                                [_0_451]  in
                                              (_0_452, body, None)))) None
                                         body.FStar_Syntax_Syntax.pos
                                        in
                                     let bind_inst =
                                       let uu____5098 =
                                         (FStar_Syntax_Subst.compress
                                            bind_repr).FStar_Syntax_Syntax.n
                                          in
                                       match uu____5098 with
                                       | FStar_Syntax_Syntax.Tm_uinst
                                           (bind,uu____5102::uu____5103::[])
                                           ->
                                           (FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_uinst
                                                 (let _0_456 =
                                                    let _0_455 =
                                                      (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                        cfg.tcenv
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let _0_454 =
                                                      let _0_453 =
                                                        (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.tcenv t
                                                         in
                                                      [_0_453]  in
                                                    _0_455 :: _0_454  in
                                                  (bind, _0_456)))) None
                                             t.FStar_Syntax_Syntax.pos
                                       | uu____5120 ->
                                           failwith
                                             "NIY : Reification of indexed effects"
                                        in
                                     let reified =
                                       (FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_app
                                             (let _0_468 =
                                                let _0_467 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                   in
                                                let _0_466 =
                                                  let _0_465 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t
                                                     in
                                                  let _0_464 =
                                                    let _0_463 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        FStar_Syntax_Syntax.tun
                                                       in
                                                    let _0_462 =
                                                      let _0_461 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          head
                                                         in
                                                      let _0_460 =
                                                        let _0_459 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            FStar_Syntax_Syntax.tun
                                                           in
                                                        let _0_458 =
                                                          let _0_457 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              body
                                                             in
                                                          [_0_457]  in
                                                        _0_459 :: _0_458  in
                                                      _0_461 :: _0_460  in
                                                    _0_463 :: _0_462  in
                                                  _0_465 :: _0_464  in
                                                _0_467 :: _0_466  in
                                              (bind_inst, _0_468)))) None
                                         t.FStar_Syntax_Syntax.pos
                                        in
                                     let _0_469 = FStar_List.tl stack  in
                                     norm cfg env _0_469 reified
                                 | FStar_Util.Inr uu____5137 ->
                                     failwith
                                       "Cannot reify a top-level let binding"))
                       | FStar_Syntax_Syntax.Tm_app (head,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m
                              in
                           let uu____5155 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____5155 with
                            | (uu____5156,bind_repr) ->
                                let maybe_unfold_action head =
                                  let maybe_extract_fv t =
                                    let t =
                                      let uu____5179 =
                                        (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                         in
                                      match uu____5179 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t,uu____5183) -> t
                                      | uu____5188 -> head  in
                                    let uu____5189 =
                                      (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                       in
                                    match uu____5189 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____5192 -> None  in
                                  let uu____5193 = maybe_extract_fv head  in
                                  match uu____5193 with
                                  | Some x when
                                      let _0_470 =
                                        FStar_Syntax_Syntax.lid_of_fv x  in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv _0_470
                                      ->
                                      let head = norm cfg env [] head  in
                                      let action_unfolded =
                                        let uu____5202 =
                                          maybe_extract_fv head  in
                                        match uu____5202 with
                                        | Some uu____5205 -> Some true
                                        | uu____5206 -> Some false  in
                                      (head, action_unfolded)
                                  | uu____5209 -> (head, None)  in
                                let rec bind_on_lift args acc =
                                  match args with
                                  | [] ->
                                      (match FStar_List.rev acc with
                                       | [] ->
                                           failwith
                                             "bind_on_lift should be always called with a non-empty list"
                                       | (head,uu____5256)::args ->
                                           let uu____5271 =
                                             maybe_unfold_action head  in
                                           (match uu____5271 with
                                            | (head,found_action) ->
                                                let mk tm =
                                                  (FStar_Syntax_Syntax.mk tm)
                                                    None
                                                    t.FStar_Syntax_Syntax.pos
                                                   in
                                                let body =
                                                  mk
                                                    (FStar_Syntax_Syntax.Tm_app
                                                       (head, args))
                                                   in
                                                (match found_action with
                                                 | None  ->
                                                     FStar_Syntax_Util.mk_reify
                                                       body
                                                 | Some (false ) ->
                                                     mk
                                                       (FStar_Syntax_Syntax.Tm_meta
                                                          (body,
                                                            (FStar_Syntax_Syntax.Meta_monadic
                                                               (m, t))))
                                                 | Some (true ) -> body)))
                                  | (e,q)::es ->
                                      let uu____5317 =
                                        (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
                                         in
                                      (match uu____5317 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (m1,m2,t'))
                                           when
                                           Prims.op_Negation
                                             (FStar_Syntax_Util.is_pure_effect
                                                m1)
                                           ->
                                           let x =
                                             FStar_Syntax_Syntax.gen_bv
                                               "monadic_app_var" None t'
                                              in
                                           let body =
                                             let _0_473 =
                                               let _0_472 =
                                                 let _0_471 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x
                                                    in
                                                 (_0_471, q)  in
                                               _0_472 :: acc  in
                                             bind_on_lift es _0_473  in
                                           let lifted_e0 =
                                             reify_lift cfg.tcenv e0 m1 m2 t'
                                              in
                                           let continuation =
                                             FStar_Syntax_Util.abs
                                               [(x, None)] body
                                               (Some
                                                  (FStar_Util.Inr (m2, [])))
                                              in
                                           let bind_inst =
                                             let uu____5359 =
                                               (FStar_Syntax_Subst.compress
                                                  bind_repr).FStar_Syntax_Syntax.n
                                                in
                                             match uu____5359 with
                                             | FStar_Syntax_Syntax.Tm_uinst
                                                 (bind,uu____5363::uu____5364::[])
                                                 ->
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_uinst
                                                       (let _0_477 =
                                                          let _0_476 =
                                                            (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                              cfg.tcenv t'
                                                             in
                                                          let _0_475 =
                                                            let _0_474 =
                                                              (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                cfg.tcenv t
                                                               in
                                                            [_0_474]  in
                                                          _0_476 :: _0_475
                                                           in
                                                        (bind, _0_477))))
                                                   None
                                                   e0.FStar_Syntax_Syntax.pos
                                             | uu____5381 ->
                                                 failwith
                                                   "NIY : Reification of indexed effects"
                                              in
                                           (FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_app
                                                 (let _0_489 =
                                                    let _0_488 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t'
                                                       in
                                                    let _0_487 =
                                                      let _0_486 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      let _0_485 =
                                                        let _0_484 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            FStar_Syntax_Syntax.tun
                                                           in
                                                        let _0_483 =
                                                          let _0_482 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lifted_e0
                                                             in
                                                          let _0_481 =
                                                            let _0_480 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let _0_479 =
                                                              let _0_478 =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  continuation
                                                                 in
                                                              [_0_478]  in
                                                            _0_480 :: _0_479
                                                             in
                                                          _0_482 :: _0_481
                                                           in
                                                        _0_484 :: _0_483  in
                                                      _0_486 :: _0_485  in
                                                    _0_488 :: _0_487  in
                                                  (bind_inst, _0_489)))) None
                                             e0.FStar_Syntax_Syntax.pos
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                            uu____5396)
                                           ->
                                           bind_on_lift es ((e0, q) :: acc)
                                       | uu____5412 ->
                                           bind_on_lift es ((e, q) :: acc))
                                   in
                                let binded_head =
                                  let _0_491 =
                                    let _0_490 =
                                      FStar_Syntax_Syntax.as_arg head  in
                                    _0_490 :: args  in
                                  bind_on_lift _0_491 []  in
                                let _0_492 = FStar_List.tl stack  in
                                norm cfg env _0_492 binded_head)
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted = reify_lift cfg.tcenv e msrc mtgt t'
                              in
                           norm cfg env stack lifted
                       | uu____5435 -> norm cfg env stack head)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
                    let should_reify =
                      match stack with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____5444;
                             FStar_Syntax_Syntax.pos = uu____5445;
                             FStar_Syntax_Syntax.vars = uu____5446;_},uu____5447,uu____5448))::uu____5449
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5455 -> false  in
                    if should_reify
                    then
                      let _0_494 = FStar_List.tl stack  in
                      let _0_493 = reify_lift cfg.tcenv head m m' t  in
                      norm cfg env _0_494 _0_493
                    else
                      (let uu____5457 =
                         ((FStar_Syntax_Util.is_pure_effect m) ||
                            (FStar_Syntax_Util.is_ghost_effect m))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations))
                          in
                       if uu____5457
                       then
                         let stack = (Steps ((cfg.steps), (cfg.delta_level)))
                           :: stack  in
                         let cfg =
                           let uu___162_5462 = cfg  in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___162_5462.tcenv);
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
                | uu____5468 ->
                    (match stack with
                     | uu____5469::uu____5470 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____5474)
                              -> norm cfg env ((Meta (m, r)) :: stack) head
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args = norm_pattern_args cfg env args  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args),
                                      (t.FStar_Syntax_Syntax.pos))) :: stack)
                                head
                          | uu____5489 -> norm cfg env stack head)
                     | uu____5490 ->
                         let head = norm cfg env [] head  in
                         let m =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               FStar_Syntax_Syntax.Meta_pattern
                                 (norm_pattern_args cfg env args)
                           | uu____5500 -> m  in
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
              let uu____5514 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____5514 with
              | (uu____5515,return_repr) ->
                  let return_inst =
                    let uu____5522 =
                      (FStar_Syntax_Subst.compress return_repr).FStar_Syntax_Syntax.n
                       in
                    match uu____5522 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____5526::[])
                        ->
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_uinst
                              (let _0_496 =
                                 let _0_495 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [_0_495]  in
                               (return_tm, _0_496)))) None
                          e.FStar_Syntax_Syntax.pos
                    | uu____5543 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app
                        (let _0_500 =
                           let _0_499 = FStar_Syntax_Syntax.as_arg t  in
                           let _0_498 =
                             let _0_497 = FStar_Syntax_Syntax.as_arg e  in
                             [_0_497]  in
                           _0_499 :: _0_498  in
                         (return_inst, _0_500)))) None
                    e.FStar_Syntax_Syntax.pos
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
                (fun uu____5587  ->
                   match uu____5587 with
                   | (a,imp) ->
                       let _0_501 = norm cfg env [] a  in (_0_501, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp = ghost_to_pure_aux cfg env comp  in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___163_5608 = comp  in
            let _0_504 =
              FStar_Syntax_Syntax.Total
                (let _0_503 = norm cfg env [] t  in
                 let _0_502 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_503, _0_502))
               in
            {
              FStar_Syntax_Syntax.n = _0_504;
              FStar_Syntax_Syntax.tk = (uu___163_5608.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___163_5608.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___163_5608.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___164_5624 = comp  in
            let _0_507 =
              FStar_Syntax_Syntax.GTotal
                (let _0_506 = norm cfg env [] t  in
                 let _0_505 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_506, _0_505))
               in
            {
              FStar_Syntax_Syntax.n = _0_507;
              FStar_Syntax_Syntax.tk = (uu___164_5624.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___164_5624.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___164_5624.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5656  ->
                      match uu____5656 with
                      | (a,i) ->
                          let _0_508 = norm cfg env [] a  in (_0_508, i)))
               in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___134_5667  ->
                      match uu___134_5667 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          FStar_Syntax_Syntax.DECREASES (norm cfg env [] t)
                      | f -> f))
               in
            let uu___165_5672 = comp  in
            let _0_511 =
              FStar_Syntax_Syntax.Comp
                (let uu___166_5675 = ct  in
                 let _0_510 =
                   FStar_List.map (norm_universe cfg env)
                     ct.FStar_Syntax_Syntax.comp_univs
                    in
                 let _0_509 = norm_args ct.FStar_Syntax_Syntax.effect_args
                    in
                 {
                   FStar_Syntax_Syntax.comp_typ_name =
                     (uu___166_5675.FStar_Syntax_Syntax.comp_typ_name);
                   FStar_Syntax_Syntax.comp_univs = _0_510;
                   FStar_Syntax_Syntax.effect_args = _0_509;
                   FStar_Syntax_Syntax.flags = flags
                 })
               in
            {
              FStar_Syntax_Syntax.n = _0_511;
              FStar_Syntax_Syntax.tk = (uu___165_5672.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___165_5672.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___165_5672.FStar_Syntax_Syntax.vars)
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
            (let uu___167_5687 = cfg  in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___167_5687.tcenv);
               delta_level = (uu___167_5687.delta_level)
             }) env [] t
           in
        let non_info t =
          let _0_512 = norm t  in
          FStar_TypeChecker_Env.non_informative cfg.tcenv _0_512  in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____5694 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___168_5708 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___168_5708.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___168_5708.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_5708.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.comp_typ_name
               in
            let uu____5718 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info (FStar_TypeChecker_Env.result_typ cfg.tcenv c))
               in
            if uu____5718
            then
              let ct =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.comp_typ_name
                with
                | Some pure_eff ->
                    let uu___169_5723 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_typ_name = pure_eff;
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___169_5723.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___169_5723.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___169_5723.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                       in
                    let uu___170_5725 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_typ_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___170_5725.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___170_5725.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___170_5725.FStar_Syntax_Syntax.flags)
                    }
                 in
              let uu___171_5726 = c  in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct);
                FStar_Syntax_Syntax.tk =
                  (uu___171_5726.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___171_5726.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___171_5726.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____5732 -> c

and norm_binder :
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____5735  ->
        match uu____5735 with
        | (x,imp) ->
            let _0_514 =
              let uu___172_5738 = x  in
              let _0_513 = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___172_5738.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___172_5738.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_513
              }  in
            (_0_514, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____5742 =
          FStar_List.fold_left
            (fun uu____5749  ->
               fun b  ->
                 match uu____5749 with
                 | (nbs',env) ->
                     let b = norm_binder cfg env b  in
                     ((b :: nbs'), (Dummy :: env))) ([], env) bs
           in
        match uu____5742 with | (nbs,uu____5766) -> FStar_List.rev nbs

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
            let uu____5783 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
            if uu____5783
            then
              let u =
                let _0_515 = FStar_List.hd lc.FStar_Syntax_Syntax.lcomp_univs
                   in
                norm_universe cfg env _0_515  in
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.lcomp_res_typ
                 in
              let c =
                let uu____5790 = FStar_Syntax_Util.is_total_lcomp lc  in
                if uu____5790
                then FStar_Syntax_Syntax.mk_Total' t (Some u)
                else FStar_Syntax_Syntax.mk_GTotal' t (Some u)  in
              Some
                (FStar_Util.Inl
                   (let _0_516 = FStar_Syntax_Util.comp_set_flags c flags  in
                    FStar_TypeChecker_Env.lcomp_of_comp cfg.tcenv _0_516))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.lcomp_name), flags))
        | uu____5804 -> lopt

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
              ((let uu____5816 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms")
                   in
                if uu____5816
                then
                  let _0_518 = FStar_Syntax_Print.term_to_string tm  in
                  let _0_517 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2 "Normalized %s to %s\n" _0_518 _0_517
                else ());
               rebuild cfg env stack t)
          | (Steps (s,dl))::stack ->
              rebuild
                (let uu___173_5824 = cfg  in
                 { steps = s; tcenv = (uu___173_5824.tcenv); delta_level = dl
                 }) env stack t
          | (Meta (m,r))::stack ->
              let t = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack t
          | (MemoLazy r)::stack ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____5844  ->
                    let _0_519 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" _0_519);
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
              let _0_520 =
                let uu___174_5881 = FStar_Syntax_Util.abs bs t lopt  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___174_5881.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___174_5881.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___174_5881.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack _0_520
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack ->
              let t = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack t
          | (Arg (Clos (env,tm,m,uu____5903),aq,r))::stack ->
              (log cfg
                 (fun uu____5919  ->
                    let _0_521 = FStar_Syntax_Print.term_to_string tm  in
                    FStar_Util.print1 "Rebuilding with arg %s\n" _0_521);
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
                 (let uu____5930 = FStar_ST.read m  in
                  match uu____5930 with
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
                  | Some (uu____5956,a) ->
                      let t = FStar_Syntax_Syntax.extend_app t (a, aq) None r
                         in
                      rebuild cfg env stack t))
          | (App (head,aq,r))::stack ->
              let t = FStar_Syntax_Syntax.extend_app head (t, aq) None r  in
              let _0_522 = maybe_simplify cfg.steps t  in
              rebuild cfg env stack _0_522
          | (Match (env,branches,r))::stack ->
              (log cfg
                 (fun uu____5984  ->
                    let _0_523 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n" _0_523);
               (let scrutinee = t  in
                let norm_and_rebuild_match uu____5989 =
                  let whnf = FStar_List.contains WHNF cfg.steps  in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___135_5996  ->
                              match uu___135_5996 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____5997 -> false))
                       in
                    let steps' =
                      let uu____6000 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations)
                         in
                      if uu____6000
                      then [Exclude Zeta]
                      else [Exclude Iota; Exclude Zeta]  in
                    let uu___175_6003 = cfg  in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___175_6003.tcenv);
                      delta_level = new_delta
                    }  in
                  let norm_or_whnf env t =
                    if whnf
                    then closure_as_term cfg_exclude_iota_zeta env t
                    else norm cfg_exclude_iota_zeta env [] t  in
                  let rec norm_pat env p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____6037 -> (p, env)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                        let uu____6057 = norm_pat env hd  in
                        (match uu____6057 with
                         | (hd,env') ->
                             let tl =
                               FStar_All.pipe_right tl
                                 (FStar_List.map
                                    (fun p  -> Prims.fst (norm_pat env p)))
                                in
                             ((let uu___176_6099 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd :: tl));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___176_6099.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___176_6099.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____6116 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____6150  ->
                                  fun uu____6151  ->
                                    match (uu____6150, uu____6151) with
                                    | ((pats,env),(p,b)) ->
                                        let uu____6216 = norm_pat env p  in
                                        (match uu____6216 with
                                         | (p,env) -> (((p, b) :: pats), env)))
                               ([], env))
                           in
                        (match uu____6116 with
                         | (pats,env) ->
                             ((let uu___177_6282 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___177_6282.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___177_6282.FStar_Syntax_Syntax.p)
                               }), env))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x =
                          let uu___178_6296 = x  in
                          let _0_524 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___178_6296.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___178_6296.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_524
                          }  in
                        ((let uu___179_6300 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x);
                            FStar_Syntax_Syntax.ty =
                              (uu___179_6300.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___179_6300.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x =
                          let uu___180_6305 = x  in
                          let _0_525 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___180_6305.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___180_6305.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_525
                          }  in
                        ((let uu___181_6309 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x);
                            FStar_Syntax_Syntax.ty =
                              (uu___181_6309.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___181_6309.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                        let x =
                          let uu___182_6319 = x  in
                          let _0_526 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___182_6319.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___182_6319.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_526
                          }  in
                        let t = norm_or_whnf env t  in
                        ((let uu___183_6324 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                            FStar_Syntax_Syntax.ty =
                              (uu___183_6324.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___183_6324.FStar_Syntax_Syntax.p)
                          }), env)
                     in
                  let branches =
                    match env with
                    | [] when whnf -> branches
                    | uu____6328 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch  ->
                                let uu____6331 =
                                  FStar_Syntax_Subst.open_branch branch  in
                                match uu____6331 with
                                | (p,wopt,e) ->
                                    let uu____6349 = norm_pat env p  in
                                    (match uu____6349 with
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
                  let _0_527 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches)) r
                     in
                  rebuild cfg env stack _0_527  in
                let rec is_cons head =
                  match head.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____6386) -> is_cons h
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
                  | uu____6397 -> false  in
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
                  let uu____6496 = FStar_Syntax_Util.head_and_args scrutinee
                     in
                  match uu____6496 with
                  | (head,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p  ->
                                  let m = matches_pat scrutinee p  in
                                  match m with
                                  | FStar_Util.Inl uu____6553 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None)
                              in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____6584 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____6596 ->
                                FStar_Util.Inr
                                  (Prims.op_Negation (is_cons head)))
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____6610 =
                             (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                              in
                           (match uu____6610 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____6615 ->
                                FStar_Util.Inr
                                  (Prims.op_Negation (is_cons head))))
                
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____6649)::rest_a,(p,uu____6652)::rest_p) ->
                      let uu____6680 = matches_pat t p  in
                      (match uu____6680 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____6694 -> FStar_Util.Inr false
                 in
                let rec matches scrutinee p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p,wopt,b)::rest ->
                      let uu____6765 = matches_pat scrutinee p  in
                      (match uu____6765 with
                       | FStar_Util.Inr (false ) -> matches scrutinee rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____6775  ->
                                 let _0_530 =
                                   FStar_Syntax_Print.pat_to_string p  in
                                 let _0_529 =
                                   let _0_528 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s
                                      in
                                   FStar_All.pipe_right _0_528
                                     (FStar_String.concat "; ")
                                    in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   _0_530 _0_529);
                            (let env =
                               FStar_List.fold_left
                                 (fun env  ->
                                    fun t  ->
                                      let _0_532 =
                                        Clos
                                          (let _0_531 =
                                             FStar_Util.mk_ref (Some ([], t))
                                              in
                                           ([], t, _0_531, false))
                                         in
                                      _0_532 :: env) env s
                                in
                             let _0_533 = guard_when_clause wopt b rest  in
                             norm cfg env stack _0_533)))
                   in
                let uu____6799 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota))
                   in
                if uu____6799
                then norm_and_rebuild_match ()
                else matches scrutinee branches))

let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___136_6813  ->
                match uu___136_6813 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____6816 -> []))
         in
      let d =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____6820 -> d  in
      { steps = s; tcenv = e; delta_level = d }
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  -> fun t  -> let _0_534 = config s e  in norm _0_534 [] [] t
  
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  -> fun t  -> let _0_535 = config s e  in norm_comp _0_535 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let _0_536 = config [] env  in norm_universe _0_536 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  -> let _0_537 = config [] env  in ghost_to_pure_aux _0_537 [] c
  
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
        let _0_538 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env _0_538  in
      let uu____6863 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.lcomp_name)
          && (non_info lc.FStar_Syntax_Syntax.lcomp_res_typ)
         in
      if uu____6863
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.lcomp_name
        with
        | Some pure_eff ->
            let uu___184_6865 = lc  in
            {
              FStar_Syntax_Syntax.lcomp_name = pure_eff;
              FStar_Syntax_Syntax.lcomp_univs =
                (uu___184_6865.FStar_Syntax_Syntax.lcomp_univs);
              FStar_Syntax_Syntax.lcomp_indices =
                (uu___184_6865.FStar_Syntax_Syntax.lcomp_indices);
              FStar_Syntax_Syntax.lcomp_res_typ =
                (uu___184_6865.FStar_Syntax_Syntax.lcomp_res_typ);
              FStar_Syntax_Syntax.lcomp_cflags =
                (uu___184_6865.FStar_Syntax_Syntax.lcomp_cflags);
              FStar_Syntax_Syntax.lcomp_as_comp =
                ((fun uu____6866  ->
                    let _0_539 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                    ghost_to_pure env _0_539))
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
        (let _0_540 = config [AllowUnboundUniverses] env  in
         norm_comp _0_540 [] c)
  
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
                   let _0_542 =
                     FStar_Syntax_Syntax.Tm_refine
                       (let _0_541 = FStar_Syntax_Util.mk_conj phi1 phi  in
                        (y, _0_541))
                      in
                   mk _0_542 t0.FStar_Syntax_Syntax.pos
               | uu____6918 -> t)
          | uu____6919 -> t  in
        aux t
  
let eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun sort  ->
        let uu____6929 = FStar_Syntax_Util.arrow_formals_comp sort  in
        match uu____6929 with
        | (binders,c) ->
            (match binders with
             | [] -> t
             | uu____6945 ->
                 let uu____6949 =
                   FStar_All.pipe_right binders
                     FStar_Syntax_Util.args_of_binders
                    in
                 (match uu____6949 with
                  | (binders,args) ->
                      let _0_544 =
                        (FStar_Syntax_Syntax.mk_Tm_app t args) None
                          t.FStar_Syntax_Syntax.pos
                         in
                      let _0_543 =
                        Some
                          (FStar_Util.Inl
                             (FStar_TypeChecker_Env.lcomp_of_comp env c))
                         in
                      FStar_Syntax_Util.abs binders _0_544 _0_543))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____6979 =
        let _0_545 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
        (_0_545, (t.FStar_Syntax_Syntax.n))  in
      match uu____6979 with
      | (Some sort,uu____6988) ->
          let _0_546 = mk sort t.FStar_Syntax_Syntax.pos  in
          eta_expand_with_type env t _0_546
      | (uu____6990,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____6994 ->
          let uu____6998 = FStar_Syntax_Util.head_and_args t  in
          (match uu____6998 with
           | (head,args) ->
               let uu____7024 =
                 (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n  in
               (match uu____7024 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____7025,thead) ->
                    let uu____7039 =
                      FStar_Syntax_Util.arrow_formals_comp thead  in
                    (match uu____7039 with
                     | (formals,uu____7046) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____7064 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___185_7068 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___185_7068.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___185_7068.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___185_7068.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___185_7068.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___185_7068.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___185_7068.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___185_7068.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___185_7068.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___185_7068.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___185_7068.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___185_7068.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___185_7068.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___185_7068.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___185_7068.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___185_7068.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___185_7068.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___185_7068.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___185_7068.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___185_7068.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___185_7068.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___185_7068.FStar_TypeChecker_Env.qname_and_index)
                                 }) t
                               in
                            match uu____7064 with
                            | (uu____7069,ty,uu____7071) ->
                                eta_expand_with_type env t ty))
                | uu____7072 ->
                    let uu____7073 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___186_7077 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___186_7077.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___186_7077.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___186_7077.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___186_7077.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___186_7077.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___186_7077.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___186_7077.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___186_7077.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___186_7077.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___186_7077.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___186_7077.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___186_7077.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___186_7077.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___186_7077.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___186_7077.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___186_7077.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___186_7077.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___186_7077.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___186_7077.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___186_7077.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___186_7077.FStar_TypeChecker_Env.qname_and_index)
                         }) t
                       in
                    (match uu____7073 with
                     | (uu____7078,ty,uu____7080) ->
                         eta_expand_with_type env t ty)))
  