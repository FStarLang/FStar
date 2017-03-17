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
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  interpretation:
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option;}
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
    | Univ uu____227 -> "Univ"
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
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____683 ->
      failwith
        (let _0_276 = FStar_Syntax_Print.db_to_string x  in
         FStar_Util.format1 "Failed to find %s\n" _0_276)
  
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
              (fun uu____794  ->
                 fun u1  ->
                   match uu____794 with
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
              (try
                 let uu____883 = FStar_List.nth env x  in
                 match uu____883 with
                 | Univ u -> aux u
                 | Dummy  -> [u]
                 | uu____886 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____851 ->
                   let uu____852 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   (match uu____891 with
                    | true  -> [FStar_Syntax_Syntax.U_unknown]
                    | uu____893 -> failwith "Universe variable not found"))
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u2]
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
                  -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1025 -> t1
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
                        (uu___142_1557.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___142_1557.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___142_1557.FStar_Syntax_Syntax.lbeff);
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
                        (uu___143_1600.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___143_1600.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1601;
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
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1716 ->
                              (p, env2)
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
                                         (FStar_Syntax_Syntax.Pat_disj (hd2
                                            :: tl2));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___144_1784.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___144_1784.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1801 =
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
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___145_1967.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___145_1967.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x =
                                let uu___142_1849 = x  in
                                let _0_323 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___146_1981.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___142_1849.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_323
                                }  in
                              ((let uu___143_1853 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___147_1988.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___147_1988.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x =
                                let uu___144_1858 = x  in
                                let _0_324 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___148_1993.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___144_1858.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_324
                                }  in
                              ((let uu___145_1862 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___149_2000.FStar_Syntax_Syntax.ty);
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
                                    (uu___150_2010.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___146_1872.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = _0_325
                                }  in
                              let t = closure_as_term cfg env t  in
                              ((let uu___147_1877 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___151_2018.FStar_Syntax_Syntax.ty);
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
        | uu____2136 ->
            FStar_List.map
              (fun uu____2146  ->
                 match uu____2146 with
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
        let uu____2173 =
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
                              (uu___152_2242.FStar_Syntax_Syntax.ppname);
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
        | uu____2290 ->
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
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___130_2330  ->
                           match uu___130_2330 with
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
      let uu____3277 =
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
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      let steps = cfg.steps in
      let w t =
        let uu___150_3051 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___155_3354.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___155_3354.FStar_Syntax_Syntax.tk);
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
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4142::[]) ->
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
      fun stack1  ->
        fun t  ->
          let t = FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____3991  ->
               let _0_379 = FStar_Syntax_Print.tag_of_term t  in
               let _0_378 = FStar_Syntax_Print.term_to_string t  in
               let _0_377 = stack_to_string stack  in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4324
                 uu____4325 uu____4326);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4341 ->
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
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____4373;
                  FStar_Syntax_Syntax.pos = uu____4374;
                  FStar_Syntax_Syntax.vars = uu____4375;_},uu____4376)
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_quote hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
                 let uu___156_4416 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___156_4416.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___156_4416.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___156_4416.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____4445 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____4445) && (is_norm_request hd1 args))
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
                 let uu___151_4051 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___157_4458.tcenv);
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
                  FStar_Syntax_Syntax.tk = uu____4463;
                  FStar_Syntax_Syntax.pos = uu____4464;
                  FStar_Syntax_Syntax.vars = uu____4465;_},a1::a2::rest)
               ->
               let uu____4091 = FStar_Syntax_Util.head_and_args t  in
               (match uu____4091 with
                | (hd,uu____4102) ->
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
                  FStar_Syntax_Syntax.tk = uu____4594;
                  FStar_Syntax_Syntax.pos = uu____4595;
                  FStar_Syntax_Syntax.vars = uu____4596;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4182 = FStar_Syntax_Util.head_and_args t  in
               (match uu____4182 with
                | (reify_head,uu____4193) ->
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
                              (FStar_Const.Const_reflect uu____4649);
                            FStar_Syntax_Syntax.tk = uu____4650;
                            FStar_Syntax_Syntax.pos = uu____4651;
                            FStar_Syntax_Syntax.vars = uu____4652;_},a2::[])
                         -> norm cfg env stack1 (Prims.fst a2)
                     | uu____4677 ->
                         let stack2 =
                           (App
                              (reify_head, None, (t.FStar_Syntax_Syntax.pos)))
                           :: stack  in
                         norm cfg env stack a))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u = norm_universe cfg env u  in
               let _0_380 =
                 mk (FStar_Syntax_Syntax.Tm_type u) t.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack _0_380
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____4692 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               (match uu____4253 with
                | true  -> norm cfg env stack t'
                | uu____4254 ->
                    let us =
                      UnivArgs
                        (let _0_381 =
                           FStar_List.map (norm_universe cfg env) us  in
                         (_0_381, (t.FStar_Syntax_Syntax.pos)))
                       in
                    let stack = us :: stack  in norm cfg env stack t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t  in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___133_4708  ->
                         match uu___133_4708 with
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
                | uu____4265 ->
                    let r_env =
                      let _0_382 = FStar_Syntax_Syntax.range_of_fv f  in
                      FStar_TypeChecker_Env.set_range cfg.tcenv _0_382  in
                    let uu____4267 =
                      FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                        r_env
                        (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       in
                    (match uu____4267 with
                     | None  ->
                         (log cfg
                            (fun uu____4278  ->
                               FStar_Util.print "Tm_fvar case 2\n" []);
                          rebuild cfg env stack t)
                     | Some (us,t) ->
                         (log cfg
                            (fun uu____4284  ->
                               let _0_384 =
                                 FStar_Syntax_Print.term_to_string t0  in
                               let _0_383 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.print2 ">>> Unfolded %s to %s\n"
                                 _0_384 _0_383);
                          (let n = FStar_List.length us  in
                           match n > (Prims.parse_int "0") with
                           | true  ->
                               (match stack with
                                | (UnivArgs (us',uu____4291))::stack ->
                                    let env =
                                      FStar_All.pipe_right us'
                                        (FStar_List.fold_left
                                           (fun env  ->
                                              fun u  -> (Univ u) :: env) env)
                                       in
                                    norm cfg env stack t
                                | uu____4304 when
                                    FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains EraseUniverses)
                                    -> norm cfg env stack t
                                | uu____4305 ->
                                    failwith
                                      (let _0_385 =
                                         FStar_Syntax_Print.lid_to_string
                                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       FStar_Util.format1
                                         "Impossible: missing universe instantiation on %s"
                                         _0_385))
                           | uu____4310 -> norm cfg env stack t))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____4312 = lookup_bvar env x  in
               (match uu____4312 with
                | Univ uu____4313 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env,t0,r,fix) ->
                    (match (Prims.op_Negation fix) ||
                             (Prims.op_Negation
                                (FStar_List.contains (Exclude Zeta) cfg.steps))
                     with
                     | true  ->
                         let uu____4328 = FStar_ST.read r  in
                         (match uu____4328 with
                          | Some (env,t') ->
                              (log cfg
                                 (fun uu____4347  ->
                                    let _0_387 =
                                      FStar_Syntax_Print.term_to_string t  in
                                    let _0_386 =
                                      FStar_Syntax_Print.term_to_string t'
                                       in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n" _0_387
                                      _0_386);
                               (let uu____4348 =
                                  (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
                                   in
                                match uu____4348 with
                                | FStar_Syntax_Syntax.Tm_abs uu____4349 ->
                                    norm cfg env stack t'
                                | uu____4364 -> rebuild cfg env stack t'))
                          | None  -> norm cfg env ((MemoLazy r) :: stack) t0)
                     | uu____4371 -> norm cfg env stack t0))
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____4852)::uu____4853 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4858)::uu____4859 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4865,uu____4866))::stack_rest ->
                    (match c with
                     | Univ uu____4869 -> norm cfg (c :: env) stack_rest t1
                     | uu____4870 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____4873::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____4431  ->
                                         let _0_388 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4887);
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
                                           (fun uu___134_4901  ->
                                              match uu___134_4901 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____4902 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____4448  ->
                                         let _0_389 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4905);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____4459  ->
                                         let _0_390 = closure_to_string c  in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4917);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____4918 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____4467 ->
                                   let cfg =
                                     let uu___152_4475 = cfg  in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___158_4933.tcenv);
                                       delta_level =
                                         (uu___152_4475.delta_level)
                                     }  in
                                   let _0_391 = closure_as_term cfg env t  in
                                   rebuild cfg env stack _0_391)
                          | uu____4476::tl ->
                              (log cfg
                                 (fun uu____4486  ->
                                    let _0_392 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n" _0_392);
                               (let body =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg (c :: env) stack_rest body))))
                | (Steps (s,dl))::stack ->
                    norm
                      (let uu___153_4507 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___159_4970.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____4520  ->
                          let _0_393 = FStar_Syntax_Print.term_to_string t
                             in
                          FStar_Util.print1 "\tSet memo %s\n" _0_393);
                     norm cfg env stack t)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let _0_394 = closure_as_term cfg env t  in
                         rebuild cfg env stack _0_394
                     | uu____4531 ->
                         let uu____4532 =
                           FStar_Syntax_Subst.open_term' bs body  in
                         (match uu____4532 with
                          | (bs,body,opening) ->
                              let lopt =
                                match lopt with
                                | Some (FStar_Util.Inl l) ->
                                    let _0_400 =
                                      let _0_398 =
                                        let _0_396 =
                                          let _0_395 =
                                            l.FStar_Syntax_Syntax.comp ()  in
                                          FStar_Syntax_Subst.subst_comp
                                            opening _0_395
                                           in
                                        FStar_All.pipe_right _0_396
                                          FStar_Syntax_Util.lcomp_of_comp
                                         in
                                      FStar_All.pipe_right _0_398
                                        (fun _0_397  -> FStar_Util.Inl _0_397)
                                       in
                                    FStar_All.pipe_right _0_400
                                      (fun _0_399  -> Some _0_399)
                                | uu____4585 -> lopt  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env  ->
                                        fun uu____4599  -> Dummy :: env) env)
                                 in
                              (log cfg
                                 (fun uu____4604  ->
                                    let _0_401 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" _0_401);
                               norm cfg env'
                                 ((Abs
                                     (env, bs, env', lopt,
                                       (t.FStar_Syntax_Syntax.pos))) ::
                                 stack) body))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let stack =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____5122  ->
                         fun stack2  ->
                           match uu____5122 with
                           | (a,aq) ->
                               let _0_404 =
                                 Arg
                                   (let _0_403 =
                                      Clos
                                        (let _0_402 = FStar_Util.mk_ref None
                                            in
                                         (env, a, _0_402, false))
                                       in
                                    (_0_403, aq, (t.FStar_Syntax_Syntax.pos)))
                                  in
                               _0_404 :: stack) args)
                  in
               (log cfg
                  (fun uu____5168  ->
                     let uu____5169 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" _0_405);
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
                                ((let uu___154_4682 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___154_4682.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___154_4682.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t
                     | uu____4683 ->
                         let _0_406 = closure_as_term cfg env t  in
                         rebuild cfg env stack _0_406)
                | uu____4686 ->
                    let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                    let uu____4688 =
                      FStar_Syntax_Subst.open_term [(x, None)] f  in
                    (match uu____4688 with
                     | (closing,f) ->
                         let f = norm cfg (Dummy :: env) [] f  in
                         let t =
                           let _0_408 =
                             FStar_Syntax_Syntax.Tm_refine
                               (let _0_407 =
                                  FStar_Syntax_Subst.close closing f  in
                                ((let uu___155_4704 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___155_4704.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___155_4704.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), _0_407))
                              in
                           mk _0_408 t.FStar_Syntax_Syntax.pos  in
                         rebuild cfg env stack t))
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               (match FStar_List.contains WHNF cfg.steps with
                | true  ->
                    let _0_409 = closure_as_term cfg env t  in
                    rebuild cfg env stack _0_409
                | uu____4717 ->
                    let uu____4718 = FStar_Syntax_Subst.open_comp bs c  in
                    (match uu____4718 with
                     | (bs,c) ->
                         let c =
                           let _0_410 =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun uu____4729  -> Dummy :: env) env)
                              in
                           norm_comp cfg _0_410 c  in
                         let t =
                           let _0_411 = norm_binders cfg env bs  in
                           FStar_Syntax_Util.arrow _0_411 c  in
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
                | uu____4771 ->
                    let t1 = norm cfg env [] t1  in
                    (log cfg
                       (fun uu____5314  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____5327 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____5327
                        | FStar_Util.Inr c ->
                            FStar_Util.Inr (norm_comp cfg env c)
                         in
                      let _0_412 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l))
                          t.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack _0_412)))
           | FStar_Syntax_Syntax.Tm_match (head,branches) ->
               let stack =
                 (Match (env, branches, (t.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack head
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5391,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5392;
                              FStar_Syntax_Syntax.lbunivs = uu____5393;
                              FStar_Syntax_Syntax.lbtyp = uu____5394;
                              FStar_Syntax_Syntax.lbeff = uu____5395;
                              FStar_Syntax_Syntax.lbdef = uu____5396;_}::uu____5397),uu____5398)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____4871 =
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
               (match uu____4871 with
                | true  ->
                    let env =
                      let _0_414 =
                        Clos
                          (let _0_413 = FStar_Util.mk_ref None  in
                           (env, (lb.FStar_Syntax_Syntax.lbdef), _0_413,
                             false))
                         in
                      _0_414 :: env  in
                    norm cfg env stack body
                | uu____4890 ->
                    let uu____4891 =
                      let _0_417 =
                        let _0_416 =
                          let _0_415 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right _0_415
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [_0_416]  in
                      FStar_Syntax_Subst.open_term _0_417 body  in
                    (match uu____4891 with
                     | (bs,body) ->
                         let lb =
                           let uu___156_4899 = lb  in
                           let _0_423 =
                             let _0_420 =
                               let _0_418 = FStar_List.hd bs  in
                               FStar_All.pipe_right _0_418 Prims.fst  in
                             FStar_All.pipe_right _0_420
                               (fun _0_419  -> FStar_Util.Inl _0_419)
                              in
                           let _0_422 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let _0_421 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                           {
                             FStar_Syntax_Syntax.lbname = _0_423;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___156_4899.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = _0_422;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___156_4899.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = _0_421
                           }  in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env  -> fun uu____4913  -> Dummy :: env)
                                env)
                            in
                         norm cfg env'
                           ((Let (env, bs, lb, (t.FStar_Syntax_Syntax.pos)))
                           :: stack) body))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let _0_424 = closure_as_term cfg env t  in
               rebuild cfg env stack _0_424
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____5531 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____5553  ->
                        match uu____5553 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              FStar_Syntax_Syntax.bv_to_tm
                                (let uu___157_5002 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___157_5002.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___157_5002.FStar_Syntax_Syntax.sort)
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
               (match uu____4941 with
                | (rec_env,memos,uu____5062) ->
                    let uu____5077 =
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
                             let _0_426 =
                               Clos
                                 (let _0_425 = FStar_Util.mk_ref None  in
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                    _0_425, false))
                                in
                             _0_426 :: env) (Prims.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (match m with
                | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____5759;
                             FStar_Syntax_Syntax.pos = uu____5760;
                             FStar_Syntax_Syntax.vars = uu____5761;_},uu____5762,uu____5763))::uu____5764
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5161 -> false  in
                    (match Prims.op_Negation should_reify with
                     | true  ->
                         let t = norm cfg env [] t  in
                         let stack = (Steps ((cfg.steps), (cfg.delta_level)))
                           :: stack  in
                         let cfg =
                           let uu___158_5167 = cfg  in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___158_5167.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta]
                           }  in
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic (m, t)),
                                 (t.FStar_Syntax_Syntax.pos))) :: stack) head
                     | uu____5168 ->
                         let uu____5169 =
                           (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                            in
                         (match uu____5169 with
                          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body)
                              ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m
                                 in
                              let uu____5181 =
                                ed.FStar_Syntax_Syntax.bind_repr  in
                              (match uu____5181 with
                               | (uu____5182,bind_repr) ->
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
                                                (let _0_428 =
                                                   let _0_427 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       x
                                                      in
                                                   [_0_427]  in
                                                 (_0_428, body, None)))) None
                                            body.FStar_Syntax_Syntax.pos
                                           in
                                        let bind_inst =
                                          let uu____5229 =
                                            (FStar_Syntax_Subst.compress
                                               bind_repr).FStar_Syntax_Syntax.n
                                             in
                                          match uu____5229 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind,uu____5233::uu____5234::[])
                                              ->
                                              (FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_uinst
                                                    (let _0_432 =
                                                       let _0_431 =
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let _0_430 =
                                                         let _0_429 =
                                                           (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.tcenv t
                                                            in
                                                         [_0_429]  in
                                                       _0_431 :: _0_430  in
                                                     (bind, _0_432)))) None
                                                t.FStar_Syntax_Syntax.pos
                                          | uu____5251 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let reified =
                                          (FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_app
                                                (let _0_444 =
                                                   let _0_443 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let _0_442 =
                                                     let _0_441 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     let _0_440 =
                                                       let _0_439 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let _0_438 =
                                                         let _0_437 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             head
                                                            in
                                                         let _0_436 =
                                                           let _0_435 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let _0_434 =
                                                             let _0_433 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 body
                                                                in
                                                             [_0_433]  in
                                                           _0_435 :: _0_434
                                                            in
                                                         _0_437 :: _0_436  in
                                                       _0_439 :: _0_438  in
                                                     _0_441 :: _0_440  in
                                                   _0_443 :: _0_442  in
                                                 (bind_inst, _0_444)))) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        let _0_445 = FStar_List.tl stack  in
                                        norm cfg env _0_445 reified
                                    | FStar_Util.Inr uu____5268 ->
                                        failwith
                                          "Cannot reify a top-level let binding"))
                          | FStar_Syntax_Syntax.Tm_app (head,args) ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m
                                 in
                              let uu____5286 =
                                ed.FStar_Syntax_Syntax.bind_repr  in
                              (match uu____5286 with
                               | (uu____5287,bind_repr) ->
                                   let maybe_unfold_action head =
                                     let maybe_extract_fv t =
                                       let t =
                                         let uu____5310 =
                                           (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                            in
                                         match uu____5310 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (t,uu____5314) -> t
                                         | uu____5319 -> head  in
                                       let uu____5320 =
                                         (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                          in
                                       match uu____5320 with
                                       | FStar_Syntax_Syntax.Tm_fvar x ->
                                           Some x
                                       | uu____5323 -> None  in
                                     let uu____5324 = maybe_extract_fv head
                                        in
                                     match uu____5324 with
                                     | Some x when
                                         let _0_446 =
                                           FStar_Syntax_Syntax.lid_of_fv x
                                            in
                                         FStar_TypeChecker_Env.is_action
                                           cfg.tcenv _0_446
                                         ->
                                         let head = norm cfg env [] head  in
                                         let action_unfolded =
                                           let uu____5333 =
                                             maybe_extract_fv head  in
                                           match uu____5333 with
                                           | Some uu____5336 -> Some true
                                           | uu____5337 -> Some false  in
                                         (head, action_unfolded)
                                     | uu____5340 -> (head, None)  in
                                   let rec bind_on_lift args acc =
                                     match args with
                                     | [] ->
                                         (match FStar_List.rev acc with
                                          | [] ->
                                              failwith
                                                "bind_on_lift should be always called with a non-empty list"
                                          | (head,uu____5387)::args ->
                                              let uu____5402 =
                                                maybe_unfold_action head  in
                                              (match uu____5402 with
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
                                         let uu____5448 =
                                           (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
                                            in
                                         (match uu____5448 with
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
                                                let _0_449 =
                                                  let _0_448 =
                                                    let _0_447 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x
                                                       in
                                                    (_0_447, q)  in
                                                  _0_448 :: acc  in
                                                bind_on_lift es _0_449  in
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
                                                let uu____5490 =
                                                  (FStar_Syntax_Subst.compress
                                                     bind_repr).FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5490 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (bind,uu____5494::uu____5495::[])
                                                    ->
                                                    (FStar_Syntax_Syntax.mk
                                                       (FStar_Syntax_Syntax.Tm_uinst
                                                          (let _0_453 =
                                                             let _0_452 =
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv t'
                                                                in
                                                             let _0_451 =
                                                               let _0_450 =
                                                                 (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.tcenv
                                                                   t
                                                                  in
                                                               [_0_450]  in
                                                             _0_452 :: _0_451
                                                              in
                                                           (bind, _0_453))))
                                                      None
                                                      e0.FStar_Syntax_Syntax.pos
                                                | uu____5512 ->
                                                    failwith
                                                      "NIY : Reification of indexed effects"
                                                 in
                                              (FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_app
                                                    (let _0_465 =
                                                       let _0_464 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           t'
                                                          in
                                                       let _0_463 =
                                                         let _0_462 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let _0_461 =
                                                           let _0_460 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let _0_459 =
                                                             let _0_458 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 lifted_e0
                                                                in
                                                             let _0_457 =
                                                               let _0_456 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let _0_455 =
                                                                 let _0_454 =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    continuation
                                                                    in
                                                                 [_0_454]  in
                                                               _0_456 ::
                                                                 _0_455
                                                                in
                                                             _0_458 :: _0_457
                                                              in
                                                           _0_460 :: _0_459
                                                            in
                                                         _0_462 :: _0_461  in
                                                       _0_464 :: _0_463  in
                                                     (bind_inst, _0_465))))
                                                None
                                                e0.FStar_Syntax_Syntax.pos
                                          | FStar_Syntax_Syntax.Tm_meta
                                              (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                               uu____5527)
                                              ->
                                              bind_on_lift es ((e0, q) ::
                                                acc)
                                          | uu____5543 ->
                                              bind_on_lift es ((e, q) :: acc))
                                      in
                                   let binded_head =
                                     let _0_467 =
                                       let _0_466 =
                                         FStar_Syntax_Syntax.as_arg head  in
                                       _0_466 :: args  in
                                     bind_on_lift _0_467 []  in
                                   let _0_468 = FStar_List.tl stack  in
                                   norm cfg env _0_468 binded_head)
                          | FStar_Syntax_Syntax.Tm_meta
                              (e,FStar_Syntax_Syntax.Meta_monadic_lift
                               (msrc,mtgt,t'))
                              ->
                              let lifted =
                                reify_lift cfg.tcenv e msrc mtgt t'  in
                              norm cfg env stack lifted
                          | uu____5566 -> norm cfg env stack head))
                | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6381;
                             FStar_Syntax_Syntax.pos = uu____6382;
                             FStar_Syntax_Syntax.vars = uu____6383;_},uu____6384,uu____6385))::uu____6386
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5586 -> false  in
                    (match should_reify with
                     | true  ->
                         let _0_470 = FStar_List.tl stack  in
                         let _0_469 = reify_lift cfg.tcenv head m m' t  in
                         norm cfg env _0_470 _0_469
                     | uu____5587 ->
                         let uu____5588 =
                           ((FStar_Syntax_Util.is_pure_effect m) ||
                              (FStar_Syntax_Util.is_ghost_effect m))
                             &&
                             (FStar_All.pipe_right cfg.steps
                                (FStar_List.contains
                                   PureSubtermsWithinComputations))
                            in
                         (match uu____5588 with
                          | true  ->
                              let stack =
                                (Steps ((cfg.steps), (cfg.delta_level))) ::
                                stack  in
                              let cfg =
                                let uu___159_5593 = cfg  in
                                {
                                  steps =
                                    [PureSubtermsWithinComputations;
                                    Primops;
                                    AllowUnboundUniverses;
                                    EraseUniverses;
                                    Exclude Zeta];
                                  tcenv = (uu___159_5593.tcenv);
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
                          | uu____5596 ->
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m, m', t)),
                                      (head.FStar_Syntax_Syntax.pos))) ::
                                stack) head))
                | uu____5599 ->
                    (match stack with
                     | uu____5600::uu____5601 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____6414)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args = norm_pattern_args cfg env args  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args),
                                      (t.FStar_Syntax_Syntax.pos))) :: stack)
                                head
                          | uu____5620 -> norm cfg env stack head)
                     | uu____5621 ->
                         let head = norm cfg env [] head  in
                         let m =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               FStar_Syntax_Syntax.Meta_pattern
                                 (norm_pattern_args cfg env args)
                           | uu____5631 -> m  in
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
                let uu____5645 = ed.FStar_Syntax_Syntax.return_repr  in
                (match uu____5645 with
                 | (uu____5646,return_repr) ->
                     let return_inst =
                       let uu____5653 =
                         (FStar_Syntax_Subst.compress return_repr).FStar_Syntax_Syntax.n
                          in
                       match uu____5653 with
                       | FStar_Syntax_Syntax.Tm_uinst
                           (return_tm,uu____5657::[]) ->
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_uinst
                                 (let _0_472 =
                                    let _0_471 =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env t
                                       in
                                    [_0_471]  in
                                  (return_tm, _0_472)))) None
                             e.FStar_Syntax_Syntax.pos
                       | uu____5674 ->
                           failwith "NIY : Reification of indexed effects"
                        in
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app
                           (let _0_476 =
                              let _0_475 = FStar_Syntax_Syntax.as_arg t  in
                              let _0_474 =
                                let _0_473 = FStar_Syntax_Syntax.as_arg e  in
                                [_0_473]  in
                              _0_475 :: _0_474  in
                            (return_inst, _0_476)))) None
                       e.FStar_Syntax_Syntax.pos)
            | uu____5688 ->
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
                (fun uu____6605  ->
                   match uu____6605 with
                   | (a,imp) ->
                       let _0_477 = norm cfg env [] a  in (_0_477, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp = ghost_to_pure_aux cfg env comp  in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___160_5739 = comp  in
            let _0_480 =
              FStar_Syntax_Syntax.Total
                (let _0_479 = norm cfg env [] t  in
                 let _0_478 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_479, _0_478))
               in
            {
              FStar_Syntax_Syntax.n = uu____6630;
              FStar_Syntax_Syntax.tk = (uu___169_6627.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___169_6627.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_6627.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___161_5755 = comp  in
            let _0_483 =
              FStar_Syntax_Syntax.GTotal
                (let _0_482 = norm cfg env [] t  in
                 let _0_481 = FStar_Option.map (norm_universe cfg env) uopt
                    in
                 (_0_482, _0_481))
               in
            {
              FStar_Syntax_Syntax.n = uu____6656;
              FStar_Syntax_Syntax.tk = (uu___170_6653.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___170_6653.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___170_6653.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6695  ->
                      match uu____6695 with
                      | (a,i) ->
                          let _0_484 = norm cfg env [] a  in (_0_484, i)))
               in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___135_6707  ->
                      match uu___135_6707 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          FStar_Syntax_Syntax.DECREASES (norm cfg env [] t)
                      | f -> f))
               in
            let uu___162_5803 = comp  in
            let _0_488 =
              FStar_Syntax_Syntax.Comp
                (let uu___163_5806 = ct  in
                 let _0_487 =
                   FStar_List.map (norm_universe cfg env)
                     ct.FStar_Syntax_Syntax.comp_univs
                    in
                 let _0_486 =
                   norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                 let _0_485 = norm_args ct.FStar_Syntax_Syntax.effect_args
                    in
                 {
                   FStar_Syntax_Syntax.comp_univs = _0_487;
                   FStar_Syntax_Syntax.effect_name =
                     (uu___163_5806.FStar_Syntax_Syntax.effect_name);
                   FStar_Syntax_Syntax.result_typ = _0_486;
                   FStar_Syntax_Syntax.effect_args = _0_485;
                   FStar_Syntax_Syntax.flags = flags
                 })
               in
            {
              FStar_Syntax_Syntax.n = uu____6718;
              FStar_Syntax_Syntax.tk = (uu___171_6715.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___171_6715.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___171_6715.FStar_Syntax_Syntax.vars)
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
            (let uu___164_5818 = cfg  in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___164_5818.tcenv);
               delta_level = (uu___164_5818.delta_level)
             }) env [] t
           in
        let non_info t = FStar_Syntax_Util.non_informative (norm t)  in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____6750 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___165_5839 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___174_6764.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___174_6764.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___174_6764.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name
               in
            let uu____5849 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ)
               in
            (match uu____5849 with
             | true  ->
                 let ct =
                   match downgrade_ghost_effect_name
                           ct.FStar_Syntax_Syntax.effect_name
                   with
                   | Some pure_eff ->
                       let uu___166_5854 = ct  in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___166_5854.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name = pure_eff;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___166_5854.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___166_5854.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___166_5854.FStar_Syntax_Syntax.flags)
                       }
                   | None  ->
                       let ct = unfold_effect_abbrev cfg.tcenv c  in
                       let uu___167_5856 = ct  in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___167_5856.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___167_5856.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___167_5856.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___167_5856.FStar_Syntax_Syntax.flags)
                       }
                    in
                 let uu___168_5857 = c  in
                 {
                   FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct);
                   FStar_Syntax_Syntax.tk =
                     (uu___168_5857.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___168_5857.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___168_5857.FStar_Syntax_Syntax.vars)
                 }
             | uu____5862 -> c)
        | uu____5863 -> c

and norm_binder :
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____6791  ->
        match uu____6791 with
        | (x,imp) ->
            let _0_490 =
              let uu___169_5869 = x  in
              let _0_489 = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___178_6795.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___169_5869.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_489
              }  in
            (_0_490, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6802 =
          FStar_List.fold_left
            (fun uu____6809  ->
               fun b  ->
                 match uu____5880 with
                 | (nbs',env) ->
                     let b = norm_binder cfg env b  in
                     ((b :: nbs'), (Dummy :: env))) ([], env) bs
           in
        match uu____5873 with | (nbs,uu____5897) -> FStar_List.rev nbs

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
            let uu____5914 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
            (match uu____5914 with
             | true  ->
                 let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ  in
                 let uu____5919 = FStar_Syntax_Util.is_total_lcomp lc  in
                 (match uu____5919 with
                  | true  ->
                      Some
                        (FStar_Util.Inl
                           (FStar_Syntax_Util.lcomp_of_comp
                              (let _0_491 = FStar_Syntax_Syntax.mk_Total t
                                  in
                               FStar_Syntax_Util.comp_set_flags _0_491 flags)))
                  | uu____5925 ->
                      Some
                        (FStar_Util.Inl
                           (FStar_Syntax_Util.lcomp_of_comp
                              (let _0_492 = FStar_Syntax_Syntax.mk_GTotal t
                                  in
                               FStar_Syntax_Util.comp_set_flags _0_492 flags))))
             | uu____5928 ->
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____5938 -> lopt

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
              ((let uu____6895 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms")
                   in
                match uu____5950 with
                | true  ->
                    let _0_494 = FStar_Syntax_Print.term_to_string tm  in
                    let _0_493 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2 "Normalized %s to %s\n" _0_494 _0_493
                | uu____5951 -> ());
               rebuild cfg env stack t)
          | (Steps (s,dl))::stack ->
              rebuild
                (let uu___170_5958 = cfg  in
                 { steps = s; tcenv = (uu___170_5958.tcenv); delta_level = dl
                 }) env stack t
          | (Meta (m,r))::stack ->
              let t = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack t
          | (MemoLazy r)::stack ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____5978  ->
                    let _0_495 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" _0_495);
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
              let _0_496 =
                let uu___171_6015 = FStar_Syntax_Util.abs bs t lopt  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___180_6967.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___180_6967.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_6015.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack _0_496
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack ->
              let t = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack t
          | (Arg (Clos (env,tm,m,uu____6037),aq,r))::stack ->
              (log cfg
                 (fun uu____6053  ->
                    let _0_497 = FStar_Syntax_Print.term_to_string tm  in
                    FStar_Util.print1 "Rebuilding with arg %s\n" _0_497);
               (match FStar_List.contains (Exclude Iota) cfg.steps with
                | true  ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let arg = closure_as_term cfg env tm  in
                         let t =
                           FStar_Syntax_Syntax.extend_app t (arg, aq) None r
                            in
                         rebuild cfg env stack t
                     | uu____6060 ->
                         let stack = (App (t, aq, r)) :: stack  in
                         norm cfg env stack tm)
                | uu____6063 ->
                    let uu____6064 = FStar_ST.read m  in
                    (match uu____6064 with
                     | None  ->
                         (match FStar_List.contains WHNF cfg.steps with
                          | true  ->
                              let arg = closure_as_term cfg env tm  in
                              let t =
                                FStar_Syntax_Syntax.extend_app t (arg, aq)
                                  None r
                                 in
                              rebuild cfg env stack t
                          | uu____6084 ->
                              let stack = (MemoLazy m) :: (App (t, aq, r)) ::
                                stack  in
                              norm cfg env stack tm)
                     | Some (uu____6090,a) ->
                         let t =
                           FStar_Syntax_Syntax.extend_app t (a, aq) None r
                            in
                         rebuild cfg env stack t)))
          | (App (head,aq,r))::stack ->
              let t = FStar_Syntax_Syntax.extend_app head (t, aq) None r  in
              let _0_498 = maybe_simplify cfg.steps t  in
              rebuild cfg env stack _0_498
          | (Match (env,branches,r))::stack ->
              (log cfg
                 (fun uu____6118  ->
                    let _0_499 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n" _0_499);
               (let scrutinee = t  in
                let norm_and_rebuild_match uu____6123 =
                  let whnf = FStar_List.contains WHNF cfg.steps  in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___131_6130  ->
                              match uu___131_6130 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____6131 -> false))
                       in
                    let steps' =
                      let uu____6134 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations)
                         in
                      match uu____6134 with
                      | true  -> [Exclude Zeta]
                      | uu____6136 -> [Exclude Iota; Exclude Zeta]  in
                    let uu___172_6137 = cfg  in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___172_6137.tcenv);
                      delta_level = new_delta
                    }  in
                  let norm_or_whnf env t =
                    match whnf with
                    | true  -> closure_as_term cfg_exclude_iota_zeta env t
                    | uu____6147 -> norm cfg_exclude_iota_zeta env [] t  in
                  let rec norm_pat env p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____6171 -> (p, env)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                        let uu____6191 = norm_pat env hd  in
                        (match uu____6191 with
                         | (hd,env') ->
                             let tl =
                               FStar_All.pipe_right tl
                                 (FStar_List.map
                                    (fun p  -> Prims.fst (norm_pat env p)))
                                in
                             ((let uu___173_6233 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd :: tl));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___173_6233.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___173_6233.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____6250 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____6284  ->
                                  fun uu____6285  ->
                                    match (uu____6284, uu____6285) with
                                    | ((pats,env),(p,b)) ->
                                        let uu____6350 = norm_pat env p  in
                                        (match uu____6350 with
                                         | (p,env) -> (((p, b) :: pats), env)))
                               ([], env))
                           in
                        (match uu____6250 with
                         | (pats,env) ->
                             ((let uu___174_6416 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___174_6416.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___174_6416.FStar_Syntax_Syntax.p)
                               }), env))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x =
                          let uu___175_6430 = x  in
                          let _0_500 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___175_6430.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___175_6430.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_500
                          }  in
                        ((let uu___176_6434 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x);
                            FStar_Syntax_Syntax.ty =
                              (uu___176_6434.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___176_6434.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x =
                          let uu___177_6439 = x  in
                          let _0_501 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___177_6439.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___177_6439.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_501
                          }  in
                        ((let uu___178_6443 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x);
                            FStar_Syntax_Syntax.ty =
                              (uu___178_6443.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___178_6443.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                        let x =
                          let uu___179_6453 = x  in
                          let _0_502 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___179_6453.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___179_6453.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = _0_502
                          }  in
                        let t = norm_or_whnf env t  in
                        ((let uu___180_6458 = p  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                            FStar_Syntax_Syntax.ty =
                              (uu___180_6458.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___180_6458.FStar_Syntax_Syntax.p)
                          }), env)
                     in
                  let branches =
                    match env with
                    | [] when whnf -> branches
                    | uu____6462 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch  ->
                                let uu____6465 =
                                  FStar_Syntax_Subst.open_branch branch  in
                                match uu____6465 with
                                | (p,wopt,e) ->
                                    let uu____6483 = norm_pat env p  in
                                    (match uu____6483 with
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
                  let _0_503 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches)) r
                     in
                  rebuild cfg env stack _0_503  in
                let rec is_cons head =
                  match head.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____6520) -> is_cons h
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
                  | uu____6531 -> false  in
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
                  let uu____6630 = FStar_Syntax_Util.head_and_args scrutinee
                     in
                  match uu____6630 with
                  | (head,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p  ->
                                  let m = matches_pat scrutinee p  in
                                  match m with
                                  | FStar_Util.Inl uu____7681 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None)
                              in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____7712 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____7724 ->
                                let uu____7725 =
                                  let uu____7726 = is_cons head1 in
                                  Prims.op_Negation uu____7726 in
                                FStar_Util.Inr uu____7725)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____6744 =
                             (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                              in
                           (match uu____6744 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____6749 ->
                                FStar_Util.Inr
                                  (Prims.op_Negation (is_cons head))))
                
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____6783)::rest_a,(p,uu____6786)::rest_p) ->
                      let uu____6814 = matches_pat t p  in
                      (match uu____6814 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____6828 -> FStar_Util.Inr false
                 in
                let rec matches scrutinee p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p,wopt,b)::rest ->
                      let uu____6899 = matches_pat scrutinee p  in
                      (match uu____6899 with
                       | FStar_Util.Inr (false ) -> matches scrutinee rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____6909  ->
                                 let _0_506 =
                                   FStar_Syntax_Print.pat_to_string p  in
                                 let _0_505 =
                                   let _0_504 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s
                                      in
                                   FStar_All.pipe_right _0_504
                                     (FStar_String.concat "; ")
                                    in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____7911 uu____7912);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env  ->
                                    fun t  ->
                                      let _0_508 =
                                        Clos
                                          (let _0_507 =
                                             FStar_Util.mk_ref (Some ([], t))
                                              in
                                           ([], t, _0_507, false))
                                         in
                                      _0_508 :: env) env s
                                in
                             let _0_509 = guard_when_clause wopt b rest  in
                             norm cfg env stack _0_509)))
                   in
                let uu____6933 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota))
                   in
                match uu____6933 with
                | true  -> norm_and_rebuild_match ()
                | uu____6934 -> matches scrutinee branches))

let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___137_7971  ->
                match uu___137_7971 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____6950 -> []))
         in
      let d =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____6954 -> d  in
      { steps = s; tcenv = e; delta_level = d }
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  -> fun t  -> let _0_510 = config s e  in norm _0_510 [] [] t
  
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  -> fun t  -> let _0_511 = config s e  in norm_comp _0_511 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let _0_512 = config [] env  in norm_universe _0_512 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  -> let _0_513 = config [] env  in ghost_to_pure_aux _0_513 [] c
  
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
      let uu____6997 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      match uu____6997 with
      | true  ->
          (match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
           with
           | Some pure_eff ->
               let uu___181_6999 = lc  in
               {
                 FStar_Syntax_Syntax.eff_name = pure_eff;
                 FStar_Syntax_Syntax.res_typ =
                   (uu___181_6999.FStar_Syntax_Syntax.res_typ);
                 FStar_Syntax_Syntax.cflags =
                   (uu___181_6999.FStar_Syntax_Syntax.cflags);
                 FStar_Syntax_Syntax.comp =
                   ((fun uu____7000  ->
                       let _0_514 = lc.FStar_Syntax_Syntax.comp ()  in
                       ghost_to_pure env _0_514))
               }
           | None  -> lc)
      | uu____7001 -> lc
  
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
        (let _0_515 = config [AllowUnboundUniverses] env  in
         norm_comp _0_515 [] c)
  
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
                   let _0_517 =
                     FStar_Syntax_Syntax.Tm_refine
                       (let _0_516 = FStar_Syntax_Util.mk_conj phi1 phi  in
                        (y, _0_516))
                      in
                   mk _0_517 t0.FStar_Syntax_Syntax.pos
               | uu____7052 -> t)
          | uu____7053 -> t  in
        aux t
  
let eta_expand_with_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun sort  ->
      let uu____7060 = FStar_Syntax_Util.arrow_formals_comp sort  in
      match uu____7060 with
      | (binders,c) ->
          (match binders with
           | [] -> t
           | uu____8136 ->
               let uu____8140 =
                 FStar_All.pipe_right binders
                   FStar_Syntax_Util.args_of_binders
                  in
               (match uu____7080 with
                | (binders,args) ->
                    let _0_522 =
                      (FStar_Syntax_Syntax.mk_Tm_app t args) None
                        t.FStar_Syntax_Syntax.pos
                       in
                    let _0_521 =
                      let _0_520 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.lcomp_of_comp c)
                          (fun _0_518  -> FStar_Util.Inl _0_518)
                         in
                      FStar_All.pipe_right _0_520
                        (fun _0_519  -> Some _0_519)
                       in
                    FStar_Syntax_Util.abs binders _0_522 _0_521))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____7126 =
        let _0_523 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
        (_0_523, (t.FStar_Syntax_Syntax.n))  in
      match uu____7126 with
      | (Some sort,uu____7135) ->
          let _0_524 = mk sort t.FStar_Syntax_Syntax.pos  in
          eta_expand_with_type t _0_524
      | (uu____7137,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type t x.FStar_Syntax_Syntax.sort
      | uu____7141 ->
          let uu____7145 = FStar_Syntax_Util.head_and_args t  in
          (match uu____7145 with
           | (head,args) ->
               let uu____7171 =
                 (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n  in
               (match uu____7171 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____7172,thead) ->
                    let uu____7186 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____7186 with
                     | (formals,tres) ->
                         (match (FStar_List.length formals) =
                                  (FStar_List.length args)
                          with
                          | true  -> t
                          | uu____7216 ->
                              let uu____7217 =
                                env.FStar_TypeChecker_Env.type_of
                                  (let uu___182_7221 = env  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___182_7221.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___182_7221.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___182_7221.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___182_7221.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___182_7221.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___182_7221.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       None;
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___182_7221.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___182_7221.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___182_7221.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___182_7221.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___182_7221.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___182_7221.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___182_7221.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___182_7221.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___182_7221.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___182_7221.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___182_7221.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___182_7221.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___182_7221.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___182_7221.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       true;
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___182_7221.FStar_TypeChecker_Env.qname_and_index)
                                   }) t
                                 in
                              (match uu____7217 with
                               | (uu____7222,ty,uu____7224) ->
                                   eta_expand_with_type t ty)))
                | uu____7225 ->
                    let uu____7226 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___183_7230 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___193_8308.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___193_8308.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___193_8308.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___193_8308.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___193_8308.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___193_8308.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___193_8308.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___193_8308.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___193_8308.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___193_8308.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___193_8308.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___193_8308.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___193_8308.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___193_8308.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___193_8308.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___193_8308.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___193_8308.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___193_8308.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___193_8308.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___193_8308.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___183_7230.FStar_TypeChecker_Env.qname_and_index)
                         }) t
                       in
                    (match uu____7226 with
                     | (uu____7231,ty,uu____7233) ->
                         eta_expand_with_type t ty)))
  