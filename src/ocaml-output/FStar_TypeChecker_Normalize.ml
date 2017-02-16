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
  fun uu___123_174  ->
    match uu___123_174 with
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
    let _0_270 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right _0_270 (FStar_String.concat "; ")
  
let stack_elt_to_string : stack_elt -> Prims.string =
  fun uu___124_591  ->
    match uu___124_591 with
    | Arg (c,uu____593,uu____594) ->
        let _0_271 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" _0_271
    | MemoLazy uu____595 -> "MemoLazy"
    | Abs (uu____599,bs,uu____601,uu____602,uu____603) ->
        let _0_272 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" _0_272
    | UnivArgs uu____614 -> "UnivArgs"
    | Match uu____618 -> "Match"
    | App (t,uu____623,uu____624) ->
        let _0_273 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" _0_273
    | Meta (m,uu____626) -> "Meta"
    | Let uu____627 -> "Let"
    | Steps (s,uu____633) -> "Steps"
    | Debug t ->
        let _0_274 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" _0_274
  
let stack_to_string : stack_elt Prims.list -> Prims.string =
  fun s  ->
    let _0_275 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right _0_275 (FStar_String.concat "; ")
  
let log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____654 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      match uu____654 with | true  -> f () | uu____655 -> ()
  
let is_empty uu___125_663 =
  match uu___125_663 with | [] -> true | uu____665 -> false 
let lookup_bvar env x =
  FStar_All.try_with
    (fun uu___134_681  ->
       match () with | () -> FStar_List.nth env x.FStar_Syntax_Syntax.index)
    (fun uu___133_682  ->
       match uu___133_682 with
       | uu____683 ->
           failwith
             (let _0_276 = FStar_Syntax_Print.db_to_string x  in
              FStar_Util.format1 "Failed to find %s\n" _0_276))
  
let comp_to_comp_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ
  =
  fun env  ->
    fun c  ->
      let c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,None ) ->
            let u = env.FStar_TypeChecker_Env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (Some u)
        | FStar_Syntax_Syntax.GTotal (t,None ) ->
            let u = env.FStar_TypeChecker_Env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (Some u)
        | uu____705 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c
  
let rec unfold_effect_abbrev :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ
  =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____713 =
        FStar_TypeChecker_Env.lookup_effect_abbrev env
          c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name
         in
      match uu____713 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____723 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____723 with
           | (binders,cdef) ->
               ((match (FStar_List.length binders) <>
                         ((FStar_List.length
                             c.FStar_Syntax_Syntax.effect_args)
                            + (Prims.parse_int "1"))
                 with
                 | true  ->
                     Prims.raise
                       (FStar_Errors.Error
                          (let _0_280 =
                             let _0_279 =
                               FStar_Util.string_of_int
                                 (FStar_List.length binders)
                                in
                             let _0_278 =
                               FStar_Util.string_of_int
                                 ((FStar_List.length
                                     c.FStar_Syntax_Syntax.effect_args)
                                    + (Prims.parse_int "1"))
                                in
                             let _0_277 =
                               FStar_Syntax_Print.comp_to_string
                                 (FStar_Syntax_Syntax.mk_Comp c)
                                in
                             FStar_Util.format3
                               "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                               _0_279 _0_278 _0_277
                              in
                           (_0_280, (comp.FStar_Syntax_Syntax.pos))))
                 | uu____752 -> ());
                (let inst =
                   let _0_282 =
                     let _0_281 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     _0_281 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____761  ->
                        fun uu____762  ->
                          match (uu____761, uu____762) with
                          | ((x,uu____776),(t,uu____778)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders _0_282
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef  in
                 let c =
                   let _0_283 =
                     let uu___135_793 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___135_793.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___135_793.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___135_793.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___135_793.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right _0_283 FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c)))
  
let downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun l  ->
    match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid with
    | true  -> Some FStar_Syntax_Const.effect_Pure_lid
    | uu____799 ->
        (match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid
         with
         | true  -> Some FStar_Syntax_Const.effect_Tot_lid
         | uu____801 ->
             (match FStar_Ident.lid_equals l
                      FStar_Syntax_Const.effect_GHOST_lid
              with
              | true  -> Some FStar_Syntax_Const.effect_PURE_lid
              | uu____803 -> None))
  
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
          let uu____824 =
            FStar_List.fold_left
              (fun uu____833  ->
                 fun u  ->
                   match uu____833 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____848 = FStar_Syntax_Util.univ_kernel u  in
                       (match uu____848 with
                        | (k_u,n) ->
                            let uu____857 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            (match uu____857 with
                             | true  -> (cur_kernel, u, out)
                             | uu____863 -> (k_u, u, (cur_max :: out)))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us
             in
          match uu____824 with
          | (uu____867,u,out) -> FStar_List.rev (u :: out)  in
        let rec aux u =
          let u = FStar_Syntax_Subst.compress_univ u  in
          match u with
          | FStar_Syntax_Syntax.U_bvar x ->
              FStar_All.try_with
                (fun uu___137_881  ->
                   match () with
                   | () ->
                       let uu____883 = FStar_List.nth env x  in
                       (match uu____883 with
                        | Univ u -> aux u
                        | Dummy  -> [u]
                        | uu____886 ->
                            failwith
                              "Impossible: universe variable bound to a term"))
                (fun uu___136_888  ->
                   match uu___136_888 with
                   | uu____890 ->
                       let uu____891 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains AllowUnboundUniverses)
                          in
                       (match uu____891 with
                        | true  -> [FStar_Syntax_Syntax.U_unknown]
                        | uu____893 -> failwith "Universe variable not found"))
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us =
                let _0_284 = FStar_List.collect aux us  in
                FStar_All.pipe_right _0_284 norm_univs  in
              (match us with
               | u_k::hd::rest ->
                   let rest = hd :: rest  in
                   let uu____910 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____910 with
                    | (FStar_Syntax_Syntax.U_zero ,n) ->
                        let uu____915 =
                          FStar_All.pipe_right rest
                            (FStar_List.for_all
                               (fun u  ->
                                  let uu____918 =
                                    FStar_Syntax_Util.univ_kernel u  in
                                  match uu____918 with
                                  | (uu____921,m) -> n <= m))
                           in
                        (match uu____915 with
                         | true  -> rest
                         | uu____924 -> us)
                    | uu____925 -> us)
               | uu____928 -> us)
          | FStar_Syntax_Syntax.U_succ u ->
              let _0_286 = aux u  in
              FStar_List.map
                (fun _0_285  -> FStar_Syntax_Syntax.U_succ _0_285) _0_286
           in
        let uu____931 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        match uu____931 with
        | true  -> FStar_Syntax_Syntax.U_unknown
        | uu____932 ->
            let uu____933 = aux u  in
            (match uu____933 with
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
          (fun uu____1030  ->
             let _0_288 = FStar_Syntax_Print.tag_of_term t  in
             let _0_287 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" _0_288 _0_287);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1031 ->
             let t = FStar_Syntax_Subst.compress t  in
             (match t.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1034 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t
              | FStar_Syntax_Syntax.Tm_uvar uu____1058 -> t
              | FStar_Syntax_Syntax.Tm_type u ->
                  let _0_289 =
                    FStar_Syntax_Syntax.Tm_type (norm_universe cfg env u)  in
                  mk _0_289 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
                  let _0_290 = FStar_List.map (norm_universe cfg env) us  in
                  FStar_Syntax_Syntax.mk_Tm_uinst t _0_290
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1075 = lookup_bvar env x  in
                  (match uu____1075 with
                   | Univ uu____1076 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t
                   | Clos (env,t0,r,uu____1080) -> closure_as_term cfg env t0)
              | FStar_Syntax_Syntax.Tm_app (head,args) ->
                  let head = closure_as_term_delayed cfg env head  in
                  let args = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head, args))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1148 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1148 with
                   | (bs,env) ->
                       let body = closure_as_term_delayed cfg env body  in
                       let _0_292 =
                         FStar_Syntax_Syntax.Tm_abs
                           (let _0_291 = close_lcomp_opt cfg env lopt  in
                            (bs, body, _0_291))
                          in
                       mk _0_292 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1191 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1191 with
                   | (bs,env) ->
                       let c = close_comp cfg env c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                         t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1222 =
                    let _0_294 =
                      let _0_293 = FStar_Syntax_Syntax.mk_binder x  in
                      [_0_293]  in
                    closures_as_binders_delayed cfg env _0_294  in
                  (match uu____1222 with
                   | (x,env) ->
                       let phi = closure_as_term_delayed cfg env phi  in
                       let _0_297 =
                         FStar_Syntax_Syntax.Tm_refine
                           (let _0_296 =
                              let _0_295 = FStar_List.hd x  in
                              FStar_All.pipe_right _0_295 Prims.fst  in
                            (_0_296, phi))
                          in
                       mk _0_297 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,lopt)
                  ->
                  let _0_302 =
                    FStar_Syntax_Syntax.Tm_ascribed
                      (let _0_301 = closure_as_term_delayed cfg env t1  in
                       let _0_300 =
                         let _0_299 = closure_as_term_delayed cfg env t2  in
                         FStar_All.pipe_left
                           (fun _0_298  -> FStar_Util.Inl _0_298) _0_299
                          in
                       (_0_301, _0_300, lopt))
                     in
                  mk _0_302 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,lopt) ->
                  let _0_307 =
                    FStar_Syntax_Syntax.Tm_ascribed
                      (let _0_306 = closure_as_term_delayed cfg env t1  in
                       let _0_305 =
                         let _0_304 = close_comp cfg env c  in
                         FStar_All.pipe_left
                           (fun _0_303  -> FStar_Util.Inr _0_303) _0_304
                          in
                       (_0_306, _0_305, lopt))
                     in
                  mk _0_307 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let _0_310 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_309 = closure_as_term_delayed cfg env t'  in
                       let _0_308 =
                         FStar_Syntax_Syntax.Meta_pattern
                           (FStar_All.pipe_right args
                              (FStar_List.map
                                 (closures_as_args_delayed cfg env)))
                          in
                       (_0_309, _0_308))
                     in
                  mk _0_310 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let _0_314 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_313 = closure_as_term_delayed cfg env t'  in
                       let _0_312 =
                         FStar_Syntax_Syntax.Meta_monadic
                           (let _0_311 =
                              closure_as_term_delayed cfg env tbody  in
                            (m, _0_311))
                          in
                       (_0_313, _0_312))
                     in
                  mk _0_314 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let _0_318 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_317 = closure_as_term_delayed cfg env t'  in
                       let _0_316 =
                         FStar_Syntax_Syntax.Meta_monadic_lift
                           (let _0_315 =
                              closure_as_term_delayed cfg env tbody  in
                            (m1, m2, _0_315))
                          in
                       (_0_317, _0_316))
                     in
                  mk _0_318 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let _0_320 =
                    FStar_Syntax_Syntax.Tm_meta
                      (let _0_319 = closure_as_term_delayed cfg env t'  in
                       (_0_319, m))
                     in
                  mk _0_320 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env =
                    FStar_List.fold_left
                      (fun env  -> fun uu____1423  -> Dummy :: env) env
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
                    | FStar_Util.Inr uu____1434 -> body
                    | FStar_Util.Inl uu____1435 ->
                        closure_as_term cfg (Dummy :: env0) body
                     in
                  let lb =
                    let uu___138_1437 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___138_1437.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___138_1437.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___138_1437.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    }  in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1444,lbs),body) ->
                  let norm_one_lb env lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1468  -> fun env  -> Dummy :: env)
                        lb.FStar_Syntax_Syntax.lbunivs env
                       in
                    let env =
                      let uu____1473 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      match uu____1473 with
                      | true  -> env_univs
                      | uu____1475 ->
                          FStar_List.fold_right
                            (fun uu____1477  -> fun env  -> Dummy :: env) lbs
                            env_univs
                       in
                    let uu___139_1480 = lb  in
                    let _0_322 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let _0_321 =
                      closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___139_1480.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___139_1480.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = _0_322;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___139_1480.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = _0_321
                    }  in
                  let lbs =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1489  -> fun env  -> Dummy :: env) lbs env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head,branches) ->
                  let head = closure_as_term cfg env head  in
                  let norm_one_branch env uu____1544 =
                    match uu____1544 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1590 ->
                              (p, env)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                              let uu____1610 = norm_pat env hd  in
                              (match uu____1610 with
                               | (hd,env') ->
                                   let tl =
                                     FStar_All.pipe_right tl
                                       (FStar_List.map
                                          (fun p  ->
                                             Prims.fst (norm_pat env p)))
                                      in
                                   ((let uu___140_1652 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd ::
                                            tl));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___140_1652.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___140_1652.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1669 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1703  ->
                                        fun uu____1704  ->
                                          match (uu____1703, uu____1704) with
                                          | ((pats,env),(p,b)) ->
                                              let uu____1769 = norm_pat env p
                                                 in
                                              (match uu____1769 with
                                               | (p,env) ->
                                                   (((p, b) :: pats), env)))
                                     ([], env))
                                 in
                              (match uu____1669 with
                               | (pats,env) ->
                                   ((let uu___141_1835 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___141_1835.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___141_1835.FStar_Syntax_Syntax.p)
                                     }), env))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x =
                                let uu___142_1849 = x  in
                                let _0_323 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___142_1849.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___142_1849.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_323
                                }  in
                              ((let uu___143_1853 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___143_1853.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___143_1853.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x =
                                let uu___144_1858 = x  in
                                let _0_324 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___144_1858.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___144_1858.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_324
                                }  in
                              ((let uu___145_1862 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___145_1862.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___145_1862.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                              let x =
                                let uu___146_1872 = x  in
                                let _0_325 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___146_1872.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___146_1872.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_325
                                }  in
                              let t = closure_as_term cfg env t  in
                              ((let uu___147_1877 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___147_1877.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___147_1877.FStar_Syntax_Syntax.p)
                                }), env)
                           in
                        let uu____1880 = norm_pat env pat  in
                        (match uu____1880 with
                         | (pat,env) ->
                             let w_opt =
                               match w_opt with
                               | None  -> None
                               | Some w -> Some (closure_as_term cfg env w)
                                in
                             let tm = closure_as_term cfg env tm  in
                             (pat, w_opt, tm))
                     in
                  let _0_327 =
                    FStar_Syntax_Syntax.Tm_match
                      (let _0_326 =
                         FStar_All.pipe_right branches
                           (FStar_List.map (norm_one_branch env))
                          in
                       (head, _0_326))
                     in
                  mk _0_327 t.FStar_Syntax_Syntax.pos))

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
        | uu____1953 -> closure_as_term cfg env t

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
        | uu____1969 ->
            FStar_List.map
              (fun uu____1979  ->
                 match uu____1979 with
                 | (x,imp) ->
                     let _0_328 = closure_as_term_delayed cfg env x  in
                     (_0_328, imp)) args

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
        let uu____2003 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2027  ->
                  fun uu____2028  ->
                    match (uu____2027, uu____2028) with
                    | ((env,out),(b,imp)) ->
                        let b =
                          let uu___148_2072 = b  in
                          let _0_329 =
                            closure_as_term_delayed cfg env
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___148_2072.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___148_2072.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_329
                          }  in
                        let env = Dummy :: env  in (env, ((b, imp) :: out)))
               (env, []))
           in
        match uu____2003 with | (env,bs) -> ((FStar_List.rev bs), env)

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
        | uu____2117 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let _0_331 = closure_as_term_delayed cfg env t  in
                 let _0_330 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 FStar_Syntax_Syntax.mk_Total' _0_331 _0_330
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let _0_333 = closure_as_term_delayed cfg env t  in
                 let _0_332 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 FStar_Syntax_Syntax.mk_GTotal' _0_333 _0_332
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
                        (fun uu___126_2151  ->
                           match uu___126_2151 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               FStar_Syntax_Syntax.DECREASES
                                 (closure_as_term_delayed cfg env t)
                           | f -> f))
                    in
                 FStar_Syntax_Syntax.mk_Comp
                   (let uu___149_2156 = c  in
                    let _0_334 =
                      FStar_List.map (norm_universe cfg env)
                        c.FStar_Syntax_Syntax.comp_univs
                       in
                    {
                      FStar_Syntax_Syntax.comp_univs = _0_334;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___149_2156.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ = rt;
                      FStar_Syntax_Syntax.effect_args = args;
                      FStar_Syntax_Syntax.flags = flags
                    }))

and filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___127_2160  ->
            match uu___127_2160 with
            | FStar_Syntax_Syntax.DECREASES uu____2161 -> false
            | uu____2164 -> true))

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
            let uu____2192 = FStar_Syntax_Util.is_total_lcomp lc  in
            (match uu____2192 with
             | true  ->
                 Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
             | uu____2208 ->
                 let uu____2209 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                    in
                 (match uu____2209 with
                  | true  ->
                      Some
                        (FStar_Util.Inr
                           (FStar_Syntax_Const.effect_GTot_lid, flags))
                  | uu____2225 ->
                      Some
                        (FStar_Util.Inr
                           ((lc.FStar_Syntax_Syntax.eff_name), flags))))
        | uu____2235 -> lopt

let arith_ops :
  (FStar_Ident.lident * (Prims.int -> Prims.int -> FStar_Const.sconst))
    Prims.list
  =
  let int_as_const i =
    FStar_Const.Const_int
      (let _0_335 = FStar_Util.string_of_int i  in (_0_335, None))
     in
  let bool_as_const b = FStar_Const.Const_bool b  in
  let _0_344 =
    FStar_List.flatten
      (FStar_List.map
         (fun m  ->
            let _0_343 =
              let _0_336 = FStar_Syntax_Const.p2l ["FStar"; m; "add"]  in
              (_0_336, (fun x  -> fun y  -> int_as_const (x + y)))  in
            let _0_342 =
              let _0_341 =
                let _0_337 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"]  in
                (_0_337, (fun x  -> fun y  -> int_as_const (x - y)))  in
              let _0_340 =
                let _0_339 =
                  let _0_338 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"]  in
                  (_0_338, (fun x  -> fun y  -> int_as_const (x * y)))  in
                [_0_339]  in
              _0_341 :: _0_340  in
            _0_343 :: _0_342)
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
      ((fun x  -> fun y  -> int_as_const (x mod y))))] _0_344
  
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
         (let _0_345 = FStar_Syntax_Const.p2l x  in
          FStar_Syntax_Syntax.lid_as_fv _0_345
            FStar_Syntax_Syntax.Delta_constant None))
     in
  let ctor x =
    mk
      (FStar_Syntax_Syntax.Tm_fvar
         (let _0_346 = FStar_Syntax_Const.p2l x  in
          FStar_Syntax_Syntax.lid_as_fv _0_346
            FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor)))
     in
  let _0_363 =
    let _0_362 = FStar_Syntax_Const.p2l ["FStar"; "String"; "list_of_string"]
       in
    (_0_362,
      (fun s  ->
         let _0_361 = FStar_String.list_of_string s  in
         let _0_360 =
           mk
             (FStar_Syntax_Syntax.Tm_app
                (let _0_359 =
                   let _0_355 = ctor ["Prims"; "Nil"]  in
                   FStar_Syntax_Syntax.mk_Tm_uinst _0_355
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let _0_358 =
                   let _0_357 =
                     let _0_356 = name ["FStar"; "Char"; "char"]  in
                     (_0_356, (Some (FStar_Syntax_Syntax.Implicit true)))  in
                   [_0_357]  in
                 (_0_359, _0_358)))
            in
         FStar_List.fold_right
           (fun c  ->
              fun a  ->
                mk
                  (FStar_Syntax_Syntax.Tm_app
                     (let _0_354 =
                        let _0_347 = ctor ["Prims"; "Cons"]  in
                        FStar_Syntax_Syntax.mk_Tm_uinst _0_347
                          [FStar_Syntax_Syntax.U_zero]
                         in
                      let _0_353 =
                        let _0_352 =
                          let _0_348 = name ["FStar"; "Char"; "char"]  in
                          (_0_348,
                            (Some (FStar_Syntax_Syntax.Implicit true)))
                           in
                        let _0_351 =
                          let _0_350 =
                            let _0_349 =
                              mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_char c))
                               in
                            (_0_349, None)  in
                          [_0_350; (a, None)]  in
                        _0_352 :: _0_351  in
                      (_0_354, _0_353)))) _0_361 _0_360))
     in
  [_0_363] 
let reduce_equality :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let is_decidable_equality t =
      let uu____2574 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____2574 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq
      | uu____2576 -> false  in
    let is_propositional_equality t =
      let uu____2581 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____2581 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
      | uu____2583 -> false  in
    match tm.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app
        (op_eq_inst,(_typ,uu____2588)::(a1,uu____2590)::(a2,uu____2592)::[])
        when is_decidable_equality op_eq_inst ->
        let tt =
          let uu____2633 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2633 with
          | FStar_Syntax_Util.Equal  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool true)) tm.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Util.NotEqual  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool false)) tm.FStar_Syntax_Syntax.pos
          | uu____2636 -> tm  in
        tt
    | FStar_Syntax_Syntax.Tm_app (eq2_inst,_::(a1,_)::(a2,_)::[])
      |FStar_Syntax_Syntax.Tm_app (eq2_inst,(a1,_)::(a2,_)::[]) when
        is_propositional_equality eq2_inst ->
        let tt =
          let uu____2708 = FStar_Syntax_Util.eq_tm a1 a2  in
          match uu____2708 with
          | FStar_Syntax_Util.Equal  -> FStar_Syntax_Util.t_true
          | FStar_Syntax_Util.NotEqual  -> FStar_Syntax_Util.t_false
          | uu____2709 -> tm  in
        tt
    | uu____2710 -> tm
  
let find_fv fv ops =
  match fv.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_List.tryFind
        (fun uu____2735  ->
           match uu____2735 with
           | (l,uu____2739) -> FStar_Syntax_Syntax.fv_eq_lid fv l) ops
  | uu____2740 -> None 
let reduce_primops :
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let uu____2757 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops steps)
         in
      match uu____2757 with
      | true  -> tm
      | uu____2760 ->
          (match tm.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_app
               (fv,(a1,uu____2765)::(a2,uu____2767)::[]) ->
               let uu____2797 = find_fv fv arith_ops  in
               (match uu____2797 with
                | None  -> tm
                | Some (uu____2817,op) ->
                    let norm i j =
                      let c =
                        let _0_365 = FStar_Util.int_of_string i  in
                        let _0_364 = FStar_Util.int_of_string j  in
                        op _0_365 _0_364  in
                      mk (FStar_Syntax_Syntax.Tm_constant c)
                        tm.FStar_Syntax_Syntax.pos
                       in
                    let uu____2843 =
                      let _0_367 =
                        (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
                         in
                      let _0_366 =
                        (FStar_Syntax_Subst.compress a2).FStar_Syntax_Syntax.n
                         in
                      (_0_367, _0_366)  in
                    (match uu____2843 with
                     | (FStar_Syntax_Syntax.Tm_app
                        (head1,(arg1,uu____2850)::[]),FStar_Syntax_Syntax.Tm_app
                        (head2,(arg2,uu____2853)::[])) ->
                         let uu____2896 =
                           let _0_371 =
                             (FStar_Syntax_Subst.compress head1).FStar_Syntax_Syntax.n
                              in
                           let _0_370 =
                             (FStar_Syntax_Subst.compress head2).FStar_Syntax_Syntax.n
                              in
                           let _0_369 =
                             (FStar_Syntax_Subst.compress arg1).FStar_Syntax_Syntax.n
                              in
                           let _0_368 =
                             (FStar_Syntax_Subst.compress arg2).FStar_Syntax_Syntax.n
                              in
                           (_0_371, _0_370, _0_369, _0_368)  in
                         (match uu____2896 with
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
                              let _0_375 =
                                mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                                  tm.FStar_Syntax_Syntax.pos
                                 in
                              let _0_374 =
                                let _0_373 =
                                  let _0_372 = norm i j  in (_0_372, None)
                                   in
                                [_0_373]  in
                              FStar_Syntax_Util.mk_app _0_375 _0_374
                          | uu____2938 -> tm)
                     | (FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_int
                        (i,None )),FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_int (j,None ))) -> norm i j
                     | uu____2955 -> tm))
           | FStar_Syntax_Syntax.Tm_app (fv,(a1,uu____2960)::[]) ->
               let uu____2982 = find_fv fv un_ops  in
               (match uu____2982 with
                | None  -> tm
                | Some (uu____3002,op) ->
                    let uu____3018 =
                      (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
                       in
                    (match uu____3018 with
                     | FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_string (b,uu____3022)) ->
                         op (FStar_Bytes.unicode_bytes_as_string b)
                     | uu____3025 -> tm))
           | uu____3026 -> reduce_equality tm)
  
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
        let uu___150_3051 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___150_3051.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___150_3051.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___150_3051.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____3070 -> None  in
      let simplify arg = ((simp_t (Prims.fst arg)), arg)  in
      let uu____3097 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps)
         in
      match uu____3097 with
      | true  -> reduce_primops steps tm
      | uu____3100 ->
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
               let uu____3141 =
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid
                  in
               (match uu____3141 with
                | true  ->
                    let uu____3144 =
                      FStar_All.pipe_right args (FStar_List.map simplify)  in
                    (match uu____3144 with
                     | (Some (true ),_)::(_,(arg,_))::[]
                       |(_,(arg,_))::(Some (true ),_)::[] -> arg
                     | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                         w FStar_Syntax_Util.t_false
                     | uu____3312 -> tm)
                | uu____3321 ->
                    let uu____3322 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Syntax_Const.or_lid
                       in
                    (match uu____3322 with
                     | true  ->
                         let uu____3325 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify)
                            in
                         (match uu____3325 with
                          | (Some (true ),_)::_::[]|_::(Some (true ),_)::[]
                              -> w FStar_Syntax_Util.t_true
                          | (Some (false ),_)::(_,(arg,_))::[]
                            |(_,(arg,_))::(Some (false ),_)::[] -> arg
                          | uu____3493 -> tm)
                     | uu____3502 ->
                         let uu____3503 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.imp_lid
                            in
                         (match uu____3503 with
                          | true  ->
                              let uu____3506 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              (match uu____3506 with
                               | _::(Some (true ),_)::[]
                                 |(Some (false ),_)::_::[] ->
                                   w FStar_Syntax_Util.t_true
                               | (Some (true ),uu____3597)::(uu____3598,
                                                             (arg,uu____3600))::[]
                                   -> arg
                               | uu____3641 -> tm)
                          | uu____3650 ->
                              let uu____3651 =
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.not_lid
                                 in
                              (match uu____3651 with
                               | true  ->
                                   let uu____3654 =
                                     FStar_All.pipe_right args
                                       (FStar_List.map simplify)
                                      in
                                   (match uu____3654 with
                                    | (Some (true ),uu____3689)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (Some (false ),uu____3713)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____3737 -> tm)
                               | uu____3746 ->
                                   let uu____3747 =
                                     (FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Syntax_Const.forall_lid)
                                       ||
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Syntax_Const.exists_lid)
                                      in
                                   (match uu____3747 with
                                    | true  ->
                                        (match args with
                                         | (t,_)::[]
                                           |(_,Some
                                             (FStar_Syntax_Syntax.Implicit
                                             _))::(t,_)::[] ->
                                             let uu____3792 =
                                               (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                                in
                                             (match uu____3792 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (uu____3795::[],body,uu____3797)
                                                  ->
                                                  (match simp_t body with
                                                   | Some (true ) ->
                                                       w
                                                         FStar_Syntax_Util.t_true
                                                   | Some (false ) ->
                                                       w
                                                         FStar_Syntax_Util.t_false
                                                   | uu____3825 -> tm)
                                              | uu____3827 -> tm)
                                         | uu____3828 -> tm)
                                    | uu____3834 -> reduce_equality tm)))))
           | uu____3835 -> tm)
  
let is_norm_request hd args =
  let uu____3850 =
    let _0_376 = (FStar_Syntax_Util.un_uinst hd).FStar_Syntax_Syntax.n  in
    (_0_376, args)  in
  match uu____3850 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3856::uu____3857::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3860::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____3862 -> false 
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____3895 -> failwith "Impossible" 
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t = FStar_Syntax_Subst.compress t  in
          let firstn k l =
            match (FStar_List.length l) < k with
            | true  -> (l, [])
            | uu____4012 -> FStar_Util.first_N k l  in
          log cfg
            (fun uu____4014  ->
               let _0_380 = FStar_Syntax_Print.tag_of_term t  in
               let _0_379 = FStar_Syntax_Print.term_to_string t  in
               let _0_378 =
                 stack_to_string
                   (let _0_377 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left Prims.fst _0_377)
                  in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" _0_380 _0_379
                 _0_378);
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4022 ->
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
                 let uu___151_4081 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___151_4081.tcenv);
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
                  FStar_Syntax_Syntax.tk = uu____4085;
                  FStar_Syntax_Syntax.pos = uu____4086;
                  FStar_Syntax_Syntax.vars = uu____4087;_},a1::a2::rest)
               ->
               let uu____4121 = FStar_Syntax_Util.head_and_args t  in
               (match uu____4121 with
                | (hd,uu____4132) ->
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
                  FStar_Syntax_Syntax.tk = uu____4187;
                  FStar_Syntax_Syntax.pos = uu____4188;
                  FStar_Syntax_Syntax.vars = uu____4189;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4212 = FStar_Syntax_Util.head_and_args t  in
               (match uu____4212 with
                | (reify_head,uu____4223) ->
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
                              (FStar_Const.Const_reflect uu____4241);
                            FStar_Syntax_Syntax.tk = uu____4242;
                            FStar_Syntax_Syntax.pos = uu____4243;
                            FStar_Syntax_Syntax.vars = uu____4244;_},a::[])
                         -> norm cfg env stack (Prims.fst a)
                     | uu____4269 ->
                         let stack =
                           (App
                              (reify_head, None, (t.FStar_Syntax_Syntax.pos)))
                           :: stack  in
                         norm cfg env stack a))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u = norm_universe cfg env u  in
               let _0_381 =
                 mk (FStar_Syntax_Syntax.Tm_type u) t.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack _0_381
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____4283 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               (match uu____4283 with
                | true  -> norm cfg env stack t'
                | uu____4284 ->
                    let us =
                      UnivArgs
                        (let _0_382 =
                           FStar_List.map (norm_universe cfg env) us  in
                         (_0_382, (t.FStar_Syntax_Syntax.pos)))
                       in
                    let stack = us :: stack  in norm cfg env stack t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t  in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___128_4293  ->
                         match uu___128_4293 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l))
                  in
               (match Prims.op_Negation should_delta with
                | true  -> rebuild cfg env stack t
                | uu____4295 ->
                    let r_env =
                      let _0_383 = FStar_Syntax_Syntax.range_of_fv f  in
                      FStar_TypeChecker_Env.set_range cfg.tcenv _0_383  in
                    let uu____4297 =
                      FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                        r_env
                        (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       in
                    (match uu____4297 with
                     | None  ->
                         (log cfg
                            (fun uu____4308  ->
                               FStar_Util.print "Tm_fvar case 2\n" []);
                          rebuild cfg env stack t)
                     | Some (us,t) ->
                         (log cfg
                            (fun uu____4314  ->
                               let _0_385 =
                                 FStar_Syntax_Print.term_to_string t0  in
                               let _0_384 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2 ">>> Unfolded %s to %s\n"
                                 _0_385 _0_384);
                          (let n = FStar_List.length us  in
                           match n > (Prims.parse_int "0") with
                           | true  ->
                               (match stack with
                                | (UnivArgs (us',uu____4321))::stack ->
                                    let env =
                                      FStar_All.pipe_right us'
                                        (FStar_List.fold_left
                                           (fun env  ->
                                              fun u  -> (Univ u) :: env) env)
                                       in
                                    norm cfg env stack t
                                | uu____4334 when
                                    FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains EraseUniverses)
                                    -> norm cfg env stack t
                                | uu____4335 ->
                                    failwith
                                      (let _0_386 =
                                         FStar_Syntax_Print.lid_to_string
                                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       FStar_Util.format1
                                         "Impossible: missing universe instantiation on %s"
                                         _0_386))
                           | uu____4340 -> norm cfg env stack t))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____4342 = lookup_bvar env x  in
               (match uu____4342 with
                | Univ uu____4343 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env,t0,r,fix) ->
                    (match (Prims.op_Negation fix) ||
                             (Prims.op_Negation
                                (FStar_List.contains (Exclude Zeta) cfg.steps))
                     with
                     | true  ->
                         let uu____4358 = FStar_ST.read r  in
                         (match uu____4358 with
                          | Some (env,t') ->
                              (log cfg
                                 (fun uu____4377  ->
                                    let _0_388 =
                                      FStar_Syntax_Print.term_to_string t  in
                                    let _0_387 =
                                      FStar_Syntax_Print.term_to_string t'
                                       in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n" _0_388
                                      _0_387);
                               (let uu____4378 =
                                  (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
                                   in
                                match uu____4378 with
                                | FStar_Syntax_Syntax.Tm_abs uu____4379 ->
                                    norm cfg env stack t'
                                | uu____4394 -> rebuild cfg env stack t'))
                          | None  -> norm cfg env ((MemoLazy r) :: stack) t0)
                     | uu____4401 -> norm cfg env stack t0))
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____4427)::uu____4428 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4433)::uu____4434 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4440,uu____4441))::stack_rest ->
                    (match c with
                     | Univ uu____4444 -> norm cfg (c :: env) stack_rest t
                     | uu____4445 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____4448::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____4461  ->
                                         let _0_389 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_389);
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
                                           (fun uu___129_4475  ->
                                              match uu___129_4475 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____4476 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____4478  ->
                                         let _0_390 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_390);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____4489  ->
                                         let _0_391 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           _0_391);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____4490 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____4497 ->
                                   let cfg =
                                     let uu___152_4505 = cfg  in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___152_4505.tcenv);
                                       delta_level =
                                         (uu___152_4505.delta_level)
                                     }  in
                                   let _0_392 = closure_as_term cfg env t  in
                                   rebuild cfg env stack _0_392)
                          | uu____4506::tl ->
                              (log cfg
                                 (fun uu____4516  ->
                                    let _0_393 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n" _0_393);
                               (let body =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg (c :: env) stack_rest body))))
                | (Steps (s,dl))::stack ->
                    norm
                      (let uu___153_4537 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___153_4537.tcenv);
                         delta_level = dl
                       }) env stack t
                | (MemoLazy r)::stack ->
                    (set_memo r (env, t);
                     log cfg
                       (fun uu____4550  ->
                          let _0_394 = FStar_Syntax_Print.term_to_string t
                             in
                          FStar_Util.print1 "\tSet memo %s\n" _0_394);
                     norm cfg env stack t)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let _0_395 = closure_as_term cfg env t  in
                         rebuild cfg env stack _0_395
                     | uu____4561 ->
                         let uu____4562 =
                           FStar_Syntax_Subst.open_term' bs body  in
                         (match uu____4562 with
                          | (bs,body,opening) ->
                              let lopt =
                                match lopt with
                                | Some (FStar_Util.Inl l) ->
                                    let _0_401 =
                                      let _0_399 =
                                        let _0_397 =
                                          let _0_396 =
                                            l.FStar_Syntax_Syntax.comp ()  in
                                          FStar_Syntax_Subst.subst_comp
                                            opening _0_396
                                           in
                                        FStar_All.pipe_right _0_397
                                          FStar_Syntax_Util.lcomp_of_comp
                                         in
                                      FStar_All.pipe_right _0_399
                                        (fun _0_398  -> FStar_Util.Inl _0_398)
                                       in
                                    FStar_All.pipe_right _0_401
                                      (fun _0_400  -> Some _0_400)
                                | uu____4615 -> lopt  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env  ->
                                        fun uu____4629  -> Dummy :: env) env)
                                 in
                              (log cfg
                                 (fun uu____4634  ->
                                    let _0_402 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" _0_402);
                               norm cfg env'
                                 ((Abs
                                     (env, bs, env', lopt,
                                       (t.FStar_Syntax_Syntax.pos))) ::
                                 stack) body))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let stack =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____4668  ->
                         fun stack  ->
                           match uu____4668 with
                           | (a,aq) ->
                               let _0_405 =
                                 Arg
                                   (let _0_404 =
                                      Clos
                                        (let _0_403 = FStar_Util.mk_ref None
                                            in
                                         (env, a, _0_403, false))
                                       in
                                    (_0_404, aq, (t.FStar_Syntax_Syntax.pos)))
                                  in
                               _0_405 :: stack) args)
                  in
               (log cfg
                  (fun uu____4691  ->
                     let _0_406 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" _0_406);
                norm cfg env stack head)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               (match FStar_List.contains WHNF cfg.steps with
                | true  ->
                    (match (env, stack) with
                     | ([],[]) ->
                         let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                            in
                         let t =
                           mk
                             (FStar_Syntax_Syntax.Tm_refine
                                ((let uu___154_4712 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___154_4712.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___154_4712.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t
                     | uu____4713 ->
                         let _0_407 = closure_as_term cfg env t  in
                         rebuild cfg env stack _0_407)
                | uu____4716 ->
                    let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                    let uu____4718 =
                      FStar_Syntax_Subst.open_term [(x, None)] f  in
                    (match uu____4718 with
                     | (closing,f) ->
                         let f = norm cfg (Dummy :: env) [] f  in
                         let t =
                           let _0_409 =
                             FStar_Syntax_Syntax.Tm_refine
                               (let _0_408 =
                                  FStar_Syntax_Subst.close closing f  in
                                ((let uu___155_4734 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___155_4734.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___155_4734.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), _0_408))
                              in
                           mk _0_409 t.FStar_Syntax_Syntax.pos  in
                         rebuild cfg env stack t))
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               (match FStar_List.contains WHNF cfg.steps with
                | true  ->
                    let _0_410 = closure_as_term cfg env t  in
                    rebuild cfg env stack _0_410
                | uu____4747 ->
                    let uu____4748 = FStar_Syntax_Subst.open_comp bs c  in
                    (match uu____4748 with
                     | (bs,c) ->
                         let c =
                           let _0_411 =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun uu____4759  -> Dummy :: env) env)
                              in
                           norm_comp cfg _0_411 c  in
                         let t =
                           let _0_412 = norm_binders cfg env bs  in
                           FStar_Syntax_Util.arrow _0_412 c  in
                         rebuild cfg env stack t))
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
                | uu____4801 ->
                    let t1 = norm cfg env [] t1  in
                    (log cfg
                       (fun uu____4804  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc =
                        match tc with
                        | FStar_Util.Inl t ->
                            FStar_Util.Inl (norm cfg env [] t)
                        | FStar_Util.Inr c ->
                            FStar_Util.Inr (norm_comp cfg env c)
                         in
                      let _0_413 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l))
                          t.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack _0_413)))
           | FStar_Syntax_Syntax.Tm_match (head,branches) ->
               let stack =
                 (Match (env, branches, (t.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack head
           | FStar_Syntax_Syntax.Tm_let
               ((uu____4868,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____4869;
                              FStar_Syntax_Syntax.lbunivs = uu____4870;
                              FStar_Syntax_Syntax.lbtyp = uu____4871;
                              FStar_Syntax_Syntax.lbeff = uu____4872;
                              FStar_Syntax_Syntax.lbdef = uu____4873;_}::uu____4874),uu____4875)
               -> rebuild cfg env stack t
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____4901 =
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
               (match uu____4901 with
                | true  ->
                    let env =
                      let _0_415 =
                        Clos
                          (let _0_414 = FStar_Util.mk_ref None  in
                           (env, (lb.FStar_Syntax_Syntax.lbdef), _0_414,
                             false))
                         in
                      _0_415 :: env  in
                    norm cfg env stack body
                | uu____4920 ->
                    let uu____4921 =
                      let _0_418 =
                        let _0_417 =
                          let _0_416 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right _0_416
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [_0_417]  in
                      FStar_Syntax_Subst.open_term _0_418 body  in
                    (match uu____4921 with
                     | (bs,body) ->
                         let lb =
                           let uu___156_4929 = lb  in
                           let _0_424 =
                             let _0_421 =
                               let _0_419 = FStar_List.hd bs  in
                               FStar_All.pipe_right _0_419 Prims.fst  in
                             FStar_All.pipe_right _0_421
                               (fun _0_420  -> FStar_Util.Inl _0_420)
                              in
                           let _0_423 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let _0_422 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                           {
                             FStar_Syntax_Syntax.lbname = _0_424;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___156_4929.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = _0_423;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___156_4929.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = _0_422
                           }  in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env  -> fun uu____4943  -> Dummy :: env)
                                env)
                            in
                         norm cfg env'
                           ((Let (env, bs, lb, (t.FStar_Syntax_Syntax.pos)))
                           :: stack) body))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let _0_425 = closure_as_term cfg env t  in
               rebuild cfg env stack _0_425
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____4971 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____4993  ->
                        match uu____4993 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              FStar_Syntax_Syntax.bv_to_tm
                                (let uu___157_5032 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___157_5032.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___157_5032.FStar_Syntax_Syntax.sort)
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
               (match uu____4971 with
                | (rec_env,memos,uu____5092) ->
                    let uu____5107 =
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
                             let _0_427 =
                               Clos
                                 (let _0_426 = FStar_Util.mk_ref None  in
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                    _0_426, false))
                                in
                             _0_427 :: env) (Prims.snd lbs) env
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
                             FStar_Syntax_Syntax.tk = uu____5180;
                             FStar_Syntax_Syntax.pos = uu____5181;
                             FStar_Syntax_Syntax.vars = uu____5182;_},uu____5183,uu____5184))::uu____5185
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5191 -> false  in
                    (match Prims.op_Negation should_reify with
                     | true  ->
                         let t = norm cfg env [] t  in
                         let stack = (Steps ((cfg.steps), (cfg.delta_level)))
                           :: stack  in
                         let cfg =
                           let uu___158_5197 = cfg  in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___158_5197.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta]
                           }  in
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic (m, t)),
                                 (t.FStar_Syntax_Syntax.pos))) :: stack) head
                     | uu____5198 ->
                         let uu____5199 =
                           (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                            in
                         (match uu____5199 with
                          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body)
                              ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m
                                 in
                              let uu____5211 =
                                ed.FStar_Syntax_Syntax.bind_repr  in
                              (match uu____5211 with
                               | (uu____5212,bind_repr) ->
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
                                                (let _0_429 =
                                                   let _0_428 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       x
                                                      in
                                                   [_0_428]  in
                                                 (_0_429, body,
                                                   (Some
                                                      (FStar_Util.Inr (m, [])))))))
                                            None body.FStar_Syntax_Syntax.pos
                                           in
                                        let bind_inst =
                                          let uu____5263 =
                                            (FStar_Syntax_Subst.compress
                                               bind_repr).FStar_Syntax_Syntax.n
                                             in
                                          match uu____5263 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind,uu____5267::uu____5268::[])
                                              ->
                                              (FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_uinst
                                                    (let _0_433 =
                                                       let _0_432 =
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let _0_431 =
                                                         let _0_430 =
                                                           (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.tcenv t
                                                            in
                                                         [_0_430]  in
                                                       _0_432 :: _0_431  in
                                                     (bind, _0_433)))) None
                                                t.FStar_Syntax_Syntax.pos
                                          | uu____5285 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let reified =
                                          (FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_app
                                                (let _0_445 =
                                                   let _0_444 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let _0_443 =
                                                     let _0_442 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     let _0_441 =
                                                       let _0_440 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let _0_439 =
                                                         let _0_438 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             head
                                                            in
                                                         let _0_437 =
                                                           let _0_436 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let _0_435 =
                                                             let _0_434 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 body
                                                                in
                                                             [_0_434]  in
                                                           _0_436 :: _0_435
                                                            in
                                                         _0_438 :: _0_437  in
                                                       _0_440 :: _0_439  in
                                                     _0_442 :: _0_441  in
                                                   _0_444 :: _0_443  in
                                                 (bind_inst, _0_445)))) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        let _0_446 = FStar_List.tl stack  in
                                        norm cfg env _0_446 reified
                                    | FStar_Util.Inr uu____5302 ->
                                        failwith
                                          "Cannot reify a top-level let binding"))
                          | FStar_Syntax_Syntax.Tm_app (head,args) ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m
                                 in
                              let uu____5320 =
                                ed.FStar_Syntax_Syntax.bind_repr  in
                              (match uu____5320 with
                               | (uu____5321,bind_repr) ->
                                   let maybe_unfold_action head =
                                     let maybe_extract_fv t =
                                       let t =
                                         let uu____5344 =
                                           (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                            in
                                         match uu____5344 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (t,uu____5348) -> t
                                         | uu____5353 -> head  in
                                       let uu____5354 =
                                         (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                          in
                                       match uu____5354 with
                                       | FStar_Syntax_Syntax.Tm_fvar x ->
                                           Some x
                                       | uu____5357 -> None  in
                                     let uu____5358 = maybe_extract_fv head
                                        in
                                     match uu____5358 with
                                     | Some x when
                                         let _0_447 =
                                           FStar_Syntax_Syntax.lid_of_fv x
                                            in
                                         FStar_TypeChecker_Env.is_action
                                           cfg.tcenv _0_447
                                         ->
                                         let head = norm cfg env [] head  in
                                         let action_unfolded =
                                           let uu____5367 =
                                             maybe_extract_fv head  in
                                           match uu____5367 with
                                           | Some uu____5370 -> Some true
                                           | uu____5371 -> Some false  in
                                         (head, action_unfolded)
                                     | uu____5374 -> (head, None)  in
                                   let rec bind_on_lift args acc =
                                     match args with
                                     | [] ->
                                         (match FStar_List.rev acc with
                                          | [] ->
                                              failwith
                                                "bind_on_lift should be always called with a non-empty list"
                                          | (head,uu____5421)::args ->
                                              let uu____5436 =
                                                maybe_unfold_action head  in
                                              (match uu____5436 with
                                               | (head,found_action) ->
                                                   let mk tm =
                                                     (FStar_Syntax_Syntax.mk
                                                        tm) None
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
                                         let uu____5482 =
                                           (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
                                            in
                                         (match uu____5482 with
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
                                                let _0_450 =
                                                  let _0_449 =
                                                    let _0_448 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x
                                                       in
                                                    (_0_448, q)  in
                                                  _0_449 :: acc  in
                                                bind_on_lift es _0_450  in
                                              let lifted_e0 =
                                                reify_lift cfg.tcenv e0 m1 m2
                                                  t'
                                                 in
                                              let continuation =
                                                FStar_Syntax_Util.abs
                                                  [(x, None)] body
                                                  (Some
                                                     (FStar_Util.Inr (m2, [])))
                                                 in
                                              let bind_inst =
                                                let uu____5524 =
                                                  (FStar_Syntax_Subst.compress
                                                     bind_repr).FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5524 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (bind,uu____5528::uu____5529::[])
                                                    ->
                                                    (FStar_Syntax_Syntax.mk
                                                       (FStar_Syntax_Syntax.Tm_uinst
                                                          (let _0_454 =
                                                             let _0_453 =
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv t'
                                                                in
                                                             let _0_452 =
                                                               let _0_451 =
                                                                 (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.tcenv
                                                                   t
                                                                  in
                                                               [_0_451]  in
                                                             _0_453 :: _0_452
                                                              in
                                                           (bind, _0_454))))
                                                      None
                                                      e0.FStar_Syntax_Syntax.pos
                                                | uu____5546 ->
                                                    failwith
                                                      "NIY : Reification of indexed effects"
                                                 in
                                              (FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_app
                                                    (let _0_466 =
                                                       let _0_465 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           t'
                                                          in
                                                       let _0_464 =
                                                         let _0_463 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let _0_462 =
                                                           let _0_461 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let _0_460 =
                                                             let _0_459 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 lifted_e0
                                                                in
                                                             let _0_458 =
                                                               let _0_457 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let _0_456 =
                                                                 let _0_455 =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    continuation
                                                                    in
                                                                 [_0_455]  in
                                                               _0_457 ::
                                                                 _0_456
                                                                in
                                                             _0_459 :: _0_458
                                                              in
                                                           _0_461 :: _0_460
                                                            in
                                                         _0_463 :: _0_462  in
                                                       _0_465 :: _0_464  in
                                                     (bind_inst, _0_466))))
                                                None
                                                e0.FStar_Syntax_Syntax.pos
                                          | FStar_Syntax_Syntax.Tm_meta
                                              (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                               uu____5561)
                                              ->
                                              bind_on_lift es ((e0, q) ::
                                                acc)
                                          | uu____5577 ->
                                              bind_on_lift es ((e, q) :: acc))
                                      in
                                   let binded_head =
                                     let _0_468 =
                                       let _0_467 =
                                         FStar_Syntax_Syntax.as_arg head  in
                                       _0_467 :: args  in
                                     bind_on_lift _0_468 []  in
                                   let _0_469 = FStar_List.tl stack  in
                                   norm cfg env _0_469 binded_head)
                          | FStar_Syntax_Syntax.Tm_meta
                              (e,FStar_Syntax_Syntax.Meta_monadic_lift
                               (msrc,mtgt,t'))
                              ->
                              let lifted =
                                reify_lift cfg.tcenv e msrc mtgt t'  in
                              let _0_470 = FStar_List.tl stack  in
                              norm cfg env _0_470 lifted
                          | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                              let branches =
                                FStar_All.pipe_right branches
                                  (FStar_List.map
                                     (fun uu____5682  ->
                                        match uu____5682 with
                                        | (pat,wopt,tm) ->
                                            let _0_471 =
                                              FStar_Syntax_Util.mk_reify tm
                                               in
                                            (pat, wopt, _0_471)))
                                 in
                              let tm =
                                mk
                                  (FStar_Syntax_Syntax.Tm_match (e, branches))
                                  t.FStar_Syntax_Syntax.pos
                                 in
                              let _0_472 = FStar_List.tl stack  in
                              norm cfg env _0_472 tm
                          | uu____5743 -> norm cfg env stack head))
                | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
                    let should_reify =
                      match stack with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____5752;
                             FStar_Syntax_Syntax.pos = uu____5753;
                             FStar_Syntax_Syntax.vars = uu____5754;_},uu____5755,uu____5756))::uu____5757
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5763 -> false  in
                    (match should_reify with
                     | true  ->
                         let _0_474 = FStar_List.tl stack  in
                         let _0_473 = reify_lift cfg.tcenv head m m' t  in
                         norm cfg env _0_474 _0_473
                     | uu____5764 ->
                         let uu____5765 =
                           ((FStar_Syntax_Util.is_pure_effect m) ||
                              (FStar_Syntax_Util.is_ghost_effect m))
                             &&
                             (FStar_All.pipe_right cfg.steps
                                (FStar_List.contains
                                   PureSubtermsWithinComputations))
                            in
                         (match uu____5765 with
                          | true  ->
                              let stack =
                                (Steps ((cfg.steps), (cfg.delta_level))) ::
                                stack  in
                              let cfg =
                                let uu___159_5770 = cfg  in
                                {
                                  steps =
                                    [PureSubtermsWithinComputations;
                                    Primops;
                                    AllowUnboundUniverses;
                                    EraseUniverses;
                                    Exclude Zeta];
                                  tcenv = (uu___159_5770.tcenv);
                                  delta_level =
                                    [FStar_TypeChecker_Env.Inlining;
                                    FStar_TypeChecker_Env.Eager_unfolding_only]
                                }  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m, m', t)),
                                      (head.FStar_Syntax_Syntax.pos))) ::
                                stack) head
                          | uu____5773 ->
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m, m', t)),
                                      (head.FStar_Syntax_Syntax.pos))) ::
                                stack) head))
                | uu____5776 ->
                    (match stack with
                     | uu____5777::uu____5778 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____5782)
                              -> norm cfg env ((Meta (m, r)) :: stack) head
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args = norm_pattern_args cfg env args  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args),
                                      (t.FStar_Syntax_Syntax.pos))) :: stack)
                                head
                          | uu____5797 -> norm cfg env stack head)
                     | uu____5798 ->
                         let head = norm cfg env [] head  in
                         let m =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               FStar_Syntax_Syntax.Meta_pattern
                                 (norm_pattern_args cfg env args)
                           | uu____5808 -> m  in
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
            match FStar_Syntax_Util.is_pure_effect msrc with
            | true  ->
                let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
                let uu____5822 = ed.FStar_Syntax_Syntax.return_repr  in
                (match uu____5822 with
                 | (uu____5823,return_repr) ->
                     let return_inst =
                       let uu____5830 =
                         (FStar_Syntax_Subst.compress return_repr).FStar_Syntax_Syntax.n
                          in
                       match uu____5830 with
                       | FStar_Syntax_Syntax.Tm_uinst
                           (return_tm,uu____5834::[]) ->
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_uinst
                                 (let _0_476 =
                                    let _0_475 =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env t
                                       in
                                    [_0_475]  in
                                  (return_tm, _0_476)))) None
                             e.FStar_Syntax_Syntax.pos
                       | uu____5851 ->
                           failwith "NIY : Reification of indexed effects"
                        in
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app
                           (let _0_480 =
                              let _0_479 = FStar_Syntax_Syntax.as_arg t  in
                              let _0_478 =
                                let _0_477 = FStar_Syntax_Syntax.as_arg e  in
                                [_0_477]  in
                              _0_479 :: _0_478  in
                            (return_inst, _0_480)))) None
                       e.FStar_Syntax_Syntax.pos)
            | uu____5865 ->
                failwith "NYI: non pure monadic lift normalisation"

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
                (fun uu____5895  ->
                   match uu____5895 with
                   | (a,imp) ->
                       let _0_481 = norm cfg env [] a  in (_0_481, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp = ghost_to_pure_aux cfg env comp  in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___160_5916 = comp  in
            let _0_484 =
              FStar_Syntax_Syntax.Total
                (let _0_483 = norm cfg env [] t  in
                 let _0_482 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_483, _0_482))
               in
            {
              FStar_Syntax_Syntax.n = _0_484;
              FStar_Syntax_Syntax.tk = (uu___160_5916.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___160_5916.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___160_5916.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___161_5932 = comp  in
            let _0_487 =
              FStar_Syntax_Syntax.GTotal
                (let _0_486 = norm cfg env [] t  in
                 let _0_485 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_486, _0_485))
               in
            {
              FStar_Syntax_Syntax.n = _0_487;
              FStar_Syntax_Syntax.tk = (uu___161_5932.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___161_5932.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___161_5932.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5964  ->
                      match uu____5964 with
                      | (a,i) ->
                          let _0_488 = norm cfg env [] a  in (_0_488, i)))
               in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___130_5975  ->
                      match uu___130_5975 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          FStar_Syntax_Syntax.DECREASES (norm cfg env [] t)
                      | f -> f))
               in
            let uu___162_5980 = comp  in
            let _0_492 =
              FStar_Syntax_Syntax.Comp
                (let uu___163_5983 = ct  in
                 let _0_491 =
                   FStar_List.map (norm_universe cfg env)
                     ct.FStar_Syntax_Syntax.comp_univs
                    in
                 let _0_490 =
                   norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                 let _0_489 = norm_args ct.FStar_Syntax_Syntax.effect_args
                    in
                 {
                   FStar_Syntax_Syntax.comp_univs = _0_491;
                   FStar_Syntax_Syntax.effect_name =
                     (uu___163_5983.FStar_Syntax_Syntax.effect_name);
                   FStar_Syntax_Syntax.result_typ = _0_490;
                   FStar_Syntax_Syntax.effect_args = _0_489;
                   FStar_Syntax_Syntax.flags = flags
                 })
               in
            {
              FStar_Syntax_Syntax.n = _0_492;
              FStar_Syntax_Syntax.tk = (uu___162_5980.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___162_5980.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___162_5980.FStar_Syntax_Syntax.vars)
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
            (let uu___164_5995 = cfg  in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___164_5995.tcenv);
               delta_level = (uu___164_5995.delta_level)
             }) env [] t
           in
        let non_info t = FStar_Syntax_Util.non_informative (norm t)  in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____6002 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___165_6016 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___165_6016.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___165_6016.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___165_6016.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name
               in
            let uu____6026 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ)
               in
            (match uu____6026 with
             | true  ->
                 let ct =
                   match downgrade_ghost_effect_name
                           ct.FStar_Syntax_Syntax.effect_name
                   with
                   | Some pure_eff ->
                       let uu___166_6031 = ct  in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___166_6031.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name = pure_eff;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___166_6031.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___166_6031.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___166_6031.FStar_Syntax_Syntax.flags)
                       }
                   | None  ->
                       let ct = unfold_effect_abbrev cfg.tcenv c  in
                       let uu___167_6033 = ct  in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___167_6033.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___167_6033.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___167_6033.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___167_6033.FStar_Syntax_Syntax.flags)
                       }
                    in
                 let uu___168_6034 = c  in
                 {
                   FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct);
                   FStar_Syntax_Syntax.tk =
                     (uu___168_6034.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___168_6034.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___168_6034.FStar_Syntax_Syntax.vars)
                 }
             | uu____6039 -> c)
        | uu____6040 -> c

and norm_binder :
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____6043  ->
        match uu____6043 with
        | (x,imp) ->
            let _0_494 =
              let uu___169_6046 = x  in
              let _0_493 = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___169_6046.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___169_6046.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_493
              }  in
            (_0_494, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6050 =
          FStar_List.fold_left
            (fun uu____6057  ->
               fun b  ->
                 match uu____6057 with
                 | (nbs',env) ->
                     let b = norm_binder cfg env b  in
                     ((b :: nbs'), (Dummy :: env))) ([], env) bs
           in
        match uu____6050 with | (nbs,uu____6074) -> FStar_List.rev nbs

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
            let uu____6091 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
            (match uu____6091 with
             | true  ->
                 let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ  in
                 let uu____6096 = FStar_Syntax_Util.is_total_lcomp lc  in
                 (match uu____6096 with
                  | true  ->
                      Some
                        (FStar_Util.Inl
                           (FStar_Syntax_Util.lcomp_of_comp
                              (let _0_495 = FStar_Syntax_Syntax.mk_Total t
                                  in
                               FStar_Syntax_Util.comp_set_flags _0_495 flags)))
                  | uu____6102 ->
                      Some
                        (FStar_Util.Inl
                           (FStar_Syntax_Util.lcomp_of_comp
                              (let _0_496 = FStar_Syntax_Syntax.mk_GTotal t
                                  in
                               FStar_Syntax_Util.comp_set_flags _0_496 flags))))
             | uu____6105 ->
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____6115 -> lopt

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
              ((let uu____6127 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms")
                   in
                match uu____6127 with
                | true  ->
                    let _0_498 = FStar_Syntax_Print.term_to_string tm  in
                    let _0_497 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2 "Normalized %s to %s\n" _0_498 _0_497
                | uu____6128 -> ());
               rebuild cfg env stack t)
          | (Steps (s,dl))::stack ->
              rebuild
                (let uu___170_6135 = cfg  in
                 { steps = s; tcenv = (uu___170_6135.tcenv); delta_level = dl
                 }) env stack t
          | (Meta (m,r))::stack ->
              let t = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack t
          | (MemoLazy r)::stack ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____6155  ->
                    let _0_499 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" _0_499);
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
              let _0_500 =
                let uu___171_6192 = FStar_Syntax_Util.abs bs t lopt  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_6192.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___171_6192.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_6192.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack _0_500
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack ->
              let t = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack t
          | (Arg (Clos (env,tm,m,uu____6214),aq,r))::stack ->
              (log cfg
                 (fun uu____6230  ->
                    let _0_501 = FStar_Syntax_Print.term_to_string tm  in
                    FStar_Util.print1 "Rebuilding with arg %s\n" _0_501);
               (match FStar_List.contains (Exclude Iota) cfg.steps with
                | true  ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let arg = closure_as_term cfg env tm  in
                         let t =
                           FStar_Syntax_Syntax.extend_app t (arg, aq) None r
                            in
                         rebuild cfg env stack t
                     | uu____6237 ->
                         let stack = (App (t, aq, r)) :: stack  in
                         norm cfg env stack tm)
                | uu____6240 ->
                    let uu____6241 = FStar_ST.read m  in
                    (match uu____6241 with
                     | None  ->
                         (match FStar_List.contains WHNF cfg.steps with
                          | true  ->
                              let arg = closure_as_term cfg env tm  in
                              let t =
                                FStar_Syntax_Syntax.extend_app t (arg, aq)
                                  None r
                                 in
                              rebuild cfg env stack t
                          | uu____6261 ->
                              let stack = (MemoLazy m) :: (App (t, aq, r)) ::
                                stack  in
                              norm cfg env stack tm)
                     | Some (uu____6267,a) ->
                         let t =
                           FStar_Syntax_Syntax.extend_app t (a, aq) None r
                            in
                         rebuild cfg env stack t)))
          | (App (head,aq,r))::stack ->
              let t = FStar_Syntax_Syntax.extend_app head (t, aq) None r  in
              let _0_502 = maybe_simplify cfg.steps t  in
              rebuild cfg env stack _0_502
          | (Match (env,branches,r))::stack ->
              (log cfg
                 (fun uu____6295  ->
                    let _0_503 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n" _0_503);
               (let scrutinee = t  in
                let norm_and_rebuild_match uu____6300 =
                  let whnf = FStar_List.contains WHNF cfg.steps  in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___131_6307  ->
                              match uu___131_6307 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____6308 -> false))
                       in
                    let steps' =
                      let uu____6311 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations)
                         in
                      match uu____6311 with
                      | true  -> [Exclude Zeta]
                      | uu____6313 -> [Exclude Iota; Exclude Zeta]  in
                    let uu___172_6314 = cfg  in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___172_6314.tcenv);
                      delta_level = new_delta
                    }  in
                  let norm_or_whnf env t =
                    match whnf with
                    | true  -> closure_as_term cfg_exclude_iota_zeta env t
                    | uu____6324 -> norm cfg_exclude_iota_zeta env [] t  in
                  let rec norm_pat env p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____6348 -> (p, env)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                        let uu____6368 = norm_pat env hd  in
                        (match uu____6368 with
                         | (hd,env') ->
                             let tl =
                               FStar_All.pipe_right tl
                                 (FStar_List.map
                                    (fun p  -> Prims.fst (norm_pat env p)))
                                in
                             ((let uu___173_6410 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd :: tl));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___173_6410.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___173_6410.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____6427 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____6461  ->
                                  fun uu____6462  ->
                                    match (uu____6461, uu____6462) with
                                    | ((pats,env),(p,b)) ->
                                        let uu____6527 = norm_pat env p  in
                                        (match uu____6527 with
                                         | (p,env) -> (((p, b) :: pats), env)))
                               ([], env))
                           in
                        (match uu____6427 with
                         | (pats,env) ->
                             ((let uu___174_6593 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___174_6593.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___174_6593.FStar_Syntax_Syntax.p)
                               }), env))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x =
                          let uu___175_6607 = x  in
                          let _0_504 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___175_6607.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___175_6607.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_504
                          }  in
                        ((let uu___176_6611 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x);
                            FStar_Syntax_Syntax.ty =
                              (uu___176_6611.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___176_6611.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x =
                          let uu___177_6616 = x  in
                          let _0_505 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___177_6616.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___177_6616.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_505
                          }  in
                        ((let uu___178_6620 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x);
                            FStar_Syntax_Syntax.ty =
                              (uu___178_6620.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___178_6620.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                        let x =
                          let uu___179_6630 = x  in
                          let _0_506 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___179_6630.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___179_6630.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_506
                          }  in
                        let t = norm_or_whnf env t  in
                        ((let uu___180_6635 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                            FStar_Syntax_Syntax.ty =
                              (uu___180_6635.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___180_6635.FStar_Syntax_Syntax.p)
                          }), env)
                     in
                  let branches =
                    match env with
                    | [] when whnf -> branches
                    | uu____6639 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch  ->
                                let uu____6642 =
                                  FStar_Syntax_Subst.open_branch branch  in
                                match uu____6642 with
                                | (p,wopt,e) ->
                                    let uu____6660 = norm_pat env p  in
                                    (match uu____6660 with
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
                  let _0_507 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches)) r
                     in
                  rebuild cfg env stack _0_507  in
                let rec is_cons head =
                  match head.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____6697) -> is_cons h
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
                  | uu____6708 -> false  in
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
                  let uu____6807 = FStar_Syntax_Util.head_and_args scrutinee
                     in
                  match uu____6807 with
                  | (head,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p  ->
                                  let m = matches_pat scrutinee p  in
                                  match m with
                                  | FStar_Util.Inl uu____6864 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None)
                              in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____6895 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____6907 ->
                                FStar_Util.Inr
                                  (Prims.op_Negation (is_cons head)))
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____6921 =
                             (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                              in
                           (match uu____6921 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____6926 ->
                                FStar_Util.Inr
                                  (Prims.op_Negation (is_cons head))))
                
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____6960)::rest_a,(p,uu____6963)::rest_p) ->
                      let uu____6991 = matches_pat t p  in
                      (match uu____6991 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____7005 -> FStar_Util.Inr false
                 in
                let rec matches scrutinee p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p,wopt,b)::rest ->
                      let uu____7076 = matches_pat scrutinee p  in
                      (match uu____7076 with
                       | FStar_Util.Inr (false ) -> matches scrutinee rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____7086  ->
                                 let _0_510 =
                                   FStar_Syntax_Print.pat_to_string p  in
                                 let _0_509 =
                                   let _0_508 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s
                                      in
                                   FStar_All.pipe_right _0_508
                                     (FStar_String.concat "; ")
                                    in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   _0_510 _0_509);
                            (let env =
                               FStar_List.fold_left
                                 (fun env  ->
                                    fun t  ->
                                      let _0_512 =
                                        Clos
                                          (let _0_511 =
                                             FStar_Util.mk_ref (Some ([], t))
                                              in
                                           ([], t, _0_511, false))
                                         in
                                      _0_512 :: env) env s
                                in
                             let _0_513 = guard_when_clause wopt b rest  in
                             norm cfg env stack _0_513)))
                   in
                let uu____7110 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota))
                   in
                match uu____7110 with
                | true  -> norm_and_rebuild_match ()
                | uu____7111 -> matches scrutinee branches))

let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___132_7124  ->
                match uu___132_7124 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____7127 -> []))
         in
      let d =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____7131 -> d  in
      { steps = s; tcenv = e; delta_level = d }
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  -> fun t  -> let _0_514 = config s e  in norm _0_514 [] [] t
  
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  -> fun t  -> let _0_515 = config s e  in norm_comp _0_515 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let _0_516 = config [] env  in norm_universe _0_516 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  -> let _0_517 = config [] env  in ghost_to_pure_aux _0_517 [] c
  
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
      let uu____7174 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      match uu____7174 with
      | true  ->
          (match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
           with
           | Some pure_eff ->
               let uu___181_7176 = lc  in
               {
                 FStar_Syntax_Syntax.eff_name = pure_eff;
                 FStar_Syntax_Syntax.res_typ =
                   (uu___181_7176.FStar_Syntax_Syntax.res_typ);
                 FStar_Syntax_Syntax.cflags =
                   (uu___181_7176.FStar_Syntax_Syntax.cflags);
                 FStar_Syntax_Syntax.comp =
                   ((fun uu____7177  ->
                       let _0_518 = lc.FStar_Syntax_Syntax.comp ()  in
                       ghost_to_pure env _0_518))
               }
           | None  -> lc)
      | uu____7178 -> lc
  
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
        (let _0_519 = config [AllowUnboundUniverses] env  in
         norm_comp _0_519 [] c)
  
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
                   let _0_521 =
                     FStar_Syntax_Syntax.Tm_refine
                       (let _0_520 = FStar_Syntax_Util.mk_conj phi1 phi  in
                        (y, _0_520))
                      in
                   mk _0_521 t0.FStar_Syntax_Syntax.pos
               | uu____7229 -> t)
          | uu____7230 -> t  in
        aux t
  
let eta_expand_with_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun sort  ->
      let uu____7237 = FStar_Syntax_Util.arrow_formals_comp sort  in
      match uu____7237 with
      | (binders,c) ->
          (match binders with
           | [] -> t
           | uu____7253 ->
               let uu____7257 =
                 FStar_All.pipe_right binders
                   FStar_Syntax_Util.args_of_binders
                  in
               (match uu____7257 with
                | (binders,args) ->
                    let _0_526 =
                      (FStar_Syntax_Syntax.mk_Tm_app t args) None
                        t.FStar_Syntax_Syntax.pos
                       in
                    let _0_525 =
                      let _0_524 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.lcomp_of_comp c)
                          (fun _0_522  -> FStar_Util.Inl _0_522)
                         in
                      FStar_All.pipe_right _0_524
                        (fun _0_523  -> Some _0_523)
                       in
                    FStar_Syntax_Util.abs binders _0_526 _0_525))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____7303 =
        let _0_527 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
        (_0_527, (t.FStar_Syntax_Syntax.n))  in
      match uu____7303 with
      | (Some sort,uu____7312) ->
          let _0_528 = mk sort t.FStar_Syntax_Syntax.pos  in
          eta_expand_with_type t _0_528
      | (uu____7314,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type t x.FStar_Syntax_Syntax.sort
      | uu____7318 ->
          let uu____7322 = FStar_Syntax_Util.head_and_args t  in
          (match uu____7322 with
           | (head,args) ->
               let uu____7348 =
                 (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n  in
               (match uu____7348 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____7349,thead) ->
                    let uu____7363 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____7363 with
                     | (formals,tres) ->
                         (match (FStar_List.length formals) =
                                  (FStar_List.length args)
                          with
                          | true  -> t
                          | uu____7393 ->
                              let uu____7394 =
                                env.FStar_TypeChecker_Env.type_of
                                  (let uu___182_7398 = env  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___182_7398.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___182_7398.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___182_7398.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___182_7398.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___182_7398.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___182_7398.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       None;
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___182_7398.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___182_7398.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___182_7398.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___182_7398.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___182_7398.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___182_7398.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___182_7398.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___182_7398.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___182_7398.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___182_7398.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___182_7398.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___182_7398.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___182_7398.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___182_7398.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       true;
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___182_7398.FStar_TypeChecker_Env.qname_and_index)
                                   }) t
                                 in
                              (match uu____7394 with
                               | (uu____7399,ty,uu____7401) ->
                                   eta_expand_with_type t ty)))
                | uu____7402 ->
                    let uu____7403 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___183_7407 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___183_7407.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___183_7407.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___183_7407.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___183_7407.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___183_7407.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___183_7407.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___183_7407.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___183_7407.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___183_7407.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___183_7407.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___183_7407.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___183_7407.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___183_7407.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___183_7407.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___183_7407.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___183_7407.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___183_7407.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___183_7407.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___183_7407.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___183_7407.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___183_7407.FStar_TypeChecker_Env.qname_and_index)
                         }) t
                       in
                    (match uu____7403 with
                     | (uu____7408,ty,uu____7410) ->
                         eta_expand_with_type t ty)))
  