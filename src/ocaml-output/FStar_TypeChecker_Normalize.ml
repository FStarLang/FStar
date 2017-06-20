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
let uu___is_Beta : step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____12 -> false 
let uu___is_Iota : step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____16 -> false 
let uu___is_Zeta : step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____20 -> false 
let uu___is_Exclude : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____25 -> false
  
let __proj__Exclude__item___0 : step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let uu___is_WHNF : step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____36 -> false 
let uu___is_Primops : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____40 -> false
  
let uu___is_Eager_unfolding : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____44 -> false
  
let uu___is_Inlining : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____48 -> false
  
let uu___is_NoDeltaSteps : step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____52 -> false
  
let uu___is_UnfoldUntil : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____57 -> false
  
let __proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let uu___is_UnfoldTac : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____68 -> false
  
let uu___is_PureSubtermsWithinComputations : step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____72 -> false
  
let uu___is_Simplify : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____76 -> false
  
let uu___is_EraseUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____80 -> false
  
let uu___is_AllowUnboundUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____84 -> false
  
let uu___is_Reify : step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____88 -> false 
let uu___is_CompressUvars : step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____92 -> false
  
let uu___is_NoFullNorm : step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____96 -> false
  
type steps = step Prims.list
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  strong_reduction_ok: Prims.bool ;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
    }
type closure =
  | Clos of (closure Prims.list * FStar_Syntax_Syntax.term * (closure
  Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo *
  Prims.bool) 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let uu___is_Clos : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____179 -> false
  
let __proj__Clos__item___0 :
  closure ->
    (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let uu___is_Univ : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____218 -> false
  
let __proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let uu___is_Dummy : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____229 -> false
  
type env = closure Prims.list
let closure_to_string : closure -> Prims.string =
  fun uu___137_233  ->
    match uu___137_233 with
    | Clos (uu____234,t,uu____236,uu____237) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____248 -> "Univ"
    | Dummy  -> "dummy"
  
type cfg =
  {
  steps: steps ;
  tcenv: FStar_TypeChecker_Env.env ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step Prims.list }
type branches =
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term option *
    FStar_Syntax_Syntax.term) Prims.list
type subst_t = FStar_Syntax_Syntax.subst_elt Prims.list
type stack_elt =
  | Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
  
  | MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo 
  | Match of (env * branches * FStar_Range.range) 
  | Abs of (env * FStar_Syntax_Syntax.binders * env *
  FStar_Syntax_Syntax.residual_comp option * FStar_Range.range) 
  | App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range) 
  | Let of (env * FStar_Syntax_Syntax.binders *
  FStar_Syntax_Syntax.letbinding * FStar_Range.range) 
  | Steps of (steps * primitive_step Prims.list *
  FStar_TypeChecker_Env.delta_level Prims.list) 
  | Debug of FStar_Syntax_Syntax.term 
let uu___is_Arg : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____373 -> false
  
let __proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let uu___is_UnivArgs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____397 -> false
  
let __proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let uu___is_MemoLazy : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____421 -> false
  
let __proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let uu___is_Match : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____448 -> false
  
let __proj__Match__item___0 :
  stack_elt -> (env * branches * FStar_Range.range) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let uu___is_Abs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____475 -> false
  
let __proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp option * FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let uu___is_App : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____508 -> false
  
let __proj__App__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Meta : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____531 -> false
  
let __proj__Meta__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.metadata * FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let uu___is_Let : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____553 -> false
  
let __proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Steps : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____582 -> false
  
let __proj__Steps__item___0 :
  stack_elt ->
    (steps * primitive_step Prims.list * FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0 
let uu___is_Debug : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____609 -> false
  
let __proj__Debug__item___0 : stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r 
let set_memo r t =
  let uu____657 = FStar_ST.read r  in
  match uu____657 with
  | Some uu____662 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t) 
let env_to_string : closure Prims.list -> Prims.string =
  fun env  ->
    let uu____671 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____671 (FStar_String.concat "; ")
  
let stack_elt_to_string : stack_elt -> Prims.string =
  fun uu___138_676  ->
    match uu___138_676 with
    | Arg (c,uu____678,uu____679) ->
        let uu____680 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____680
    | MemoLazy uu____681 -> "MemoLazy"
    | Abs (uu____685,bs,uu____687,uu____688,uu____689) ->
        let uu____692 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____692
    | UnivArgs uu____697 -> "UnivArgs"
    | Match uu____701 -> "Match"
    | App (t,uu____706,uu____707) ->
        let uu____708 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____708
    | Meta (m,uu____710) -> "Meta"
    | Let uu____711 -> "Let"
    | Steps (uu____716,uu____717,uu____718) -> "Steps"
    | Debug t ->
        let uu____724 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____724
  
let stack_to_string : stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____730 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____730 (FStar_String.concat "; ")
  
let log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____744 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm")
         in
      if uu____744 then f () else ()
  
let is_empty uu___139_753 =
  match uu___139_753 with | [] -> true | uu____755 -> false 
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____773 ->
      let uu____774 =
        let uu____775 = FStar_Syntax_Print.db_to_string x  in
        FStar_Util.format1 "Failed to find %s\n" uu____775  in
      failwith uu____774
  
let downgrade_ghost_effect_name :
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
          let uu____806 =
            FStar_List.fold_left
              (fun uu____815  ->
                 fun u1  ->
                   match uu____815 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____830 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____830 with
                        | (k_u,n1) ->
                            let uu____839 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____839
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____806 with
          | (uu____849,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____865 = FStar_List.nth env x  in
                 match uu____865 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____868 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____872 ->
                   let uu____873 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses)
                      in
                   if uu____873
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____877 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____880 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____885 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____885 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____896 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____896 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____901 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____904 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____904 with
                                  | (uu____907,m) -> n1 <= m))
                           in
                        if uu____901 then rest1 else us1
                    | uu____911 -> us1)
               | uu____914 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____917 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____917
           in
        let uu____919 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)
           in
        if uu____919
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____921 = aux u  in
           match uu____921 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
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
          (fun uu____1009  ->
             let uu____1010 = FStar_Syntax_Print.tag_of_term t  in
             let uu____1011 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1010
               uu____1011);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1012 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1015 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1030 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1031 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1032 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1033 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1043 =
                    let uu____1044 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____1044  in
                  mk uu____1043 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1051 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1051
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1053 = lookup_bvar env x  in
                  (match uu____1053 with
                   | Univ uu____1054 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1058) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1116 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1116 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____1136 =
                         let uu____1137 =
                           let uu____1147 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____1147)  in
                         FStar_Syntax_Syntax.Tm_abs uu____1137  in
                       mk uu____1136 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1167 = closures_as_binders_delayed cfg env bs  in
                  (match uu____1167 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1198 =
                    let uu____1205 =
                      let uu____1209 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____1209]  in
                    closures_as_binders_delayed cfg env uu____1205  in
                  (match uu____1198 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____1223 =
                         let uu____1224 =
                           let uu____1229 =
                             let uu____1230 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____1230
                               FStar_Pervasives.fst
                              in
                           (uu____1229, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____1224  in
                       mk uu____1223 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1298 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____1298
                    | FStar_Util.Inr c ->
                        let uu____1312 = close_comp cfg env c  in
                        FStar_Util.Inr uu____1312
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____1327 =
                    let uu____1328 =
                      let uu____1346 = closure_as_term_delayed cfg env t11
                         in
                      (uu____1346, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1328  in
                  mk uu____1327 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1384 =
                    let uu____1385 =
                      let uu____1390 = closure_as_term_delayed cfg env t'  in
                      let uu____1393 =
                        let uu____1394 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____1394  in
                      (uu____1390, uu____1393)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1385  in
                  mk uu____1384 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1436 =
                    let uu____1437 =
                      let uu____1442 = closure_as_term_delayed cfg env t'  in
                      let uu____1445 =
                        let uu____1446 =
                          let uu____1451 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____1451)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____1446  in
                      (uu____1442, uu____1445)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1437  in
                  mk uu____1436 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1470 =
                    let uu____1471 =
                      let uu____1476 = closure_as_term_delayed cfg env t'  in
                      let uu____1479 =
                        let uu____1480 =
                          let uu____1486 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____1486)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1480  in
                      (uu____1476, uu____1479)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1471  in
                  mk uu____1470 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1499 =
                    let uu____1500 =
                      let uu____1505 = closure_as_term_delayed cfg env t'  in
                      (uu____1505, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____1500  in
                  mk uu____1499 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1526  -> Dummy :: env1) env
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
                    | FStar_Util.Inr uu____1537 -> body
                    | FStar_Util.Inl uu____1538 ->
                        closure_as_term cfg (Dummy :: env0) body
                     in
                  let lb1 =
                    let uu___153_1540 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___153_1540.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___153_1540.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___153_1540.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    }  in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1547,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1571  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____1576 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____1576
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1580  -> fun env2  -> Dummy :: env2) lbs
                          env_univs
                       in
                    let uu___154_1583 = lb  in
                    let uu____1584 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let uu____1587 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___154_1583.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___154_1583.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1584;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___154_1583.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1587
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1598  -> fun env1  -> Dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____1653 =
                    match uu____1653 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1699 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1715 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1749  ->
                                        fun uu____1750  ->
                                          match (uu____1749, uu____1750) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1815 =
                                                norm_pat env3 p1  in
                                              (match uu____1815 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____1715 with
                               | (pats1,env3) ->
                                   ((let uu___155_1881 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___155_1881.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___155_1881.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___156_1895 = x  in
                                let uu____1896 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___156_1895.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___156_1895.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1896
                                }  in
                              ((let uu___157_1902 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___157_1902.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___157_1902.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___158_1907 = x  in
                                let uu____1908 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___158_1907.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___158_1907.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1908
                                }  in
                              ((let uu___159_1914 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___159_1914.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___159_1914.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___160_1924 = x  in
                                let uu____1925 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___160_1924.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___160_1924.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1925
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___161_1932 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___161_1932.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___161_1932.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____1935 = norm_pat env1 pat  in
                        (match uu____1935 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____1959 =
                                     closure_as_term cfg env2 w  in
                                   Some uu____1959
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____1964 =
                    let uu____1965 =
                      let uu____1981 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____1981)  in
                    FStar_Syntax_Syntax.Tm_match uu____1965  in
                  mk uu____1964 t1.FStar_Syntax_Syntax.pos))

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
        | uu____2034 -> closure_as_term cfg env t

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
        | uu____2050 ->
            FStar_List.map
              (fun uu____2060  ->
                 match uu____2060 with
                 | (x,imp) ->
                     let uu____2075 = closure_as_term_delayed cfg env x  in
                     (uu____2075, imp)) args

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
        let uu____2087 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2111  ->
                  fun uu____2112  ->
                    match (uu____2111, uu____2112) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___162_2156 = b  in
                          let uu____2157 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___162_2156.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___162_2156.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2157
                          }  in
                        let env2 = Dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____2087 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____2204 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2216 = closure_as_term_delayed cfg env t  in
                 let uu____2217 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____2216 uu____2217
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2227 = closure_as_term_delayed cfg env t  in
                 let uu____2228 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2227 uu____2228
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___140_2244  ->
                           match uu___140_2244 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2248 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____2248
                           | f -> f))
                    in
                 let uu____2252 =
                   let uu___163_2253 = c1  in
                   let uu____2254 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2254;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___163_2253.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____2252)

and filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___141_2259  ->
            match uu___141_2259 with
            | FStar_Syntax_Syntax.DECREASES uu____2260 -> false
            | uu____2263 -> true))

and close_lcomp_opt :
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.residual_comp option ->
        FStar_Syntax_Syntax.residual_comp option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___142_2275  ->
                      match uu___142_2275 with
                      | FStar_Syntax_Syntax.DECREASES uu____2276 -> false
                      | uu____2279 -> true))
               in
            let rc1 =
              let uu___164_2281 = rc  in
              let uu____2282 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___164_2281.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____2282;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            Some rc1
        | uu____2288 -> lopt

let built_in_primitive_steps : primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p  in
  let int_as_const p i =
    let uu____2307 =
      let uu____2308 =
        let uu____2314 = FStar_Util.string_of_int i  in (uu____2314, None)
         in
      FStar_Const.Const_int uu____2308  in
    const_as_tm uu____2307 p  in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p  in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p
     in
  let arg_as_int uu____2341 =
    match uu____2341 with
    | (a,uu____2346) ->
        let uu____2348 =
          let uu____2349 = FStar_Syntax_Subst.compress a  in
          uu____2349.FStar_Syntax_Syntax.n  in
        (match uu____2348 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2359 = FStar_Util.int_of_string i  in Some uu____2359
         | uu____2360 -> None)
     in
  let arg_as_bounded_int uu____2369 =
    match uu____2369 with
    | (a,uu____2376) ->
        let uu____2380 =
          let uu____2381 = FStar_Syntax_Subst.compress a  in
          uu____2381.FStar_Syntax_Syntax.n  in
        (match uu____2380 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2388;
                FStar_Syntax_Syntax.pos = uu____2389;
                FStar_Syntax_Syntax.vars = uu____2390;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2392;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2393;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2394;_},uu____2395)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2426 =
               let uu____2429 = FStar_Util.int_of_string i  in
               (fv1, uu____2429)  in
             Some uu____2426
         | uu____2432 -> None)
     in
  let arg_as_bool uu____2441 =
    match uu____2441 with
    | (a,uu____2446) ->
        let uu____2448 =
          let uu____2449 = FStar_Syntax_Subst.compress a  in
          uu____2449.FStar_Syntax_Syntax.n  in
        (match uu____2448 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2454 -> None)
     in
  let arg_as_char uu____2461 =
    match uu____2461 with
    | (a,uu____2466) ->
        let uu____2468 =
          let uu____2469 = FStar_Syntax_Subst.compress a  in
          uu____2469.FStar_Syntax_Syntax.n  in
        (match uu____2468 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2474 -> None)
     in
  let arg_as_string uu____2481 =
    match uu____2481 with
    | (a,uu____2486) ->
        let uu____2488 =
          let uu____2489 = FStar_Syntax_Subst.compress a  in
          uu____2489.FStar_Syntax_Syntax.n  in
        (match uu____2488 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2494)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2497 -> None)
     in
  let arg_as_list f uu____2518 =
    match uu____2518 with
    | (a,uu____2527) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2546 -> None
          | (Some x)::xs ->
              let uu____2556 = sequence xs  in
              (match uu____2556 with
               | None  -> None
               | Some xs' -> Some (x :: xs'))
           in
        let uu____2567 = FStar_Syntax_Util.list_elements a  in
        (match uu____2567 with
         | None  -> None
         | Some elts ->
             let uu____2577 =
               FStar_List.map
                 (fun x  ->
                    let uu____2582 = FStar_Syntax_Syntax.as_arg x  in
                    f uu____2582) elts
                in
             sequence uu____2577)
     in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2612 = f a  in Some uu____2612
    | uu____2613 -> None  in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] ->
        let uu____2652 = f a0 a1  in Some uu____2652
    | uu____2653 -> None  in
  let unary_op as_a f r args =
    let uu____2697 = FStar_List.map as_a args  in lift_unary (f r) uu____2697
     in
  let binary_op as_a f r args =
    let uu____2747 = FStar_List.map as_a args  in
    lift_binary (f r) uu____2747  in
  let as_primitive_step uu____2764 =
    match uu____2764 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f }
     in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2802 = f x  in int_as_const r uu____2802)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2825 = f x y  in int_as_const r uu____2825)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  -> let uu____2842 = f x  in bool_as_const r uu____2842)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2865 = f x y  in bool_as_const r uu____2865)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____2888 = f x y  in string_as_const r uu____2888)
     in
  let list_of_string' rng s =
    let name l =
      let uu____2902 =
        let uu____2903 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____2903  in
      mk uu____2902 rng  in
    let char_t = name FStar_Syntax_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____2913 =
      let uu____2915 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____2915  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____2913  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Const.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in int_as_const rng r  in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____2969 = arg_as_string a1  in
        (match uu____2969 with
         | Some s1 ->
             let uu____2973 = arg_as_list arg_as_string a2  in
             (match uu____2973 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____2981 = string_as_const rng r  in Some uu____2981
              | uu____2982 -> None)
         | uu____2985 -> None)
    | uu____2987 -> None  in
  let string_of_int1 rng i =
    let uu____2998 = FStar_Util.string_of_int i  in
    string_as_const rng uu____2998  in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false")  in
  let string_of_int2 rng i =
    let uu____3014 = FStar_Util.string_of_int i  in
    string_as_const rng uu____3014  in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false")  in
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng
       in
    match args with
    | (_typ,uu____3043)::(a1,uu____3045)::(a2,uu____3047)::[] ->
        let uu____3076 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____3076 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____3088 -> None)
    | uu____3089 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____3101 =
      let uu____3111 =
        let uu____3121 =
          let uu____3131 =
            let uu____3141 =
              let uu____3151 =
                let uu____3161 =
                  let uu____3171 =
                    let uu____3181 =
                      let uu____3191 =
                        let uu____3201 =
                          let uu____3211 =
                            let uu____3221 =
                              let uu____3231 =
                                let uu____3241 =
                                  let uu____3251 =
                                    let uu____3261 =
                                      let uu____3271 =
                                        let uu____3281 =
                                          let uu____3291 =
                                            let uu____3300 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"]
                                               in
                                            (uu____3300,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string'))
                                             in
                                          let uu____3306 =
                                            let uu____3316 =
                                              let uu____3325 =
                                                FStar_Syntax_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"]
                                                 in
                                              (uu____3325,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list arg_as_char)
                                                   string_of_list'))
                                               in
                                            let uu____3332 =
                                              let uu____3342 =
                                                let uu____3354 =
                                                  FStar_Syntax_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"]
                                                   in
                                                (uu____3354,
                                                  (Prims.parse_int "2"),
                                                  string_concat')
                                                 in
                                              [uu____3342]  in
                                            uu____3316 :: uu____3332  in
                                          uu____3291 :: uu____3306  in
                                        (FStar_Syntax_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____3281
                                         in
                                      (FStar_Syntax_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____3271
                                       in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3261
                                     in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3251
                                   in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3241
                                 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3231
                               in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3221
                             in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3211
                           in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3201
                         in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3191
                       in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3181
                     in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3171
                   in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3161
                 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3151
               in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3141
             in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3131
           in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3121
         in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3111
       in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3101
     in
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
      "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = int_as_const r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____3704 =
        let uu____3705 =
          let uu____3706 = FStar_Syntax_Syntax.as_arg c  in [uu____3706]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3705  in
      uu____3704 None r  in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3730 =
              let uu____3739 = FStar_Syntax_Const.p2l ["FStar"; m; "add"]  in
              (uu____3739, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3748  ->
                        fun uu____3749  ->
                          match (uu____3748, uu____3749) with
                          | ((int_to_t1,x),(uu____3760,y)) ->
                              int_as_bounded r int_to_t1 (x + y))))
               in
            let uu____3766 =
              let uu____3776 =
                let uu____3785 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"]
                   in
                (uu____3785, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3794  ->
                          fun uu____3795  ->
                            match (uu____3794, uu____3795) with
                            | ((int_to_t1,x),(uu____3806,y)) ->
                                int_as_bounded r int_to_t1 (x - y))))
                 in
              let uu____3812 =
                let uu____3822 =
                  let uu____3831 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"]
                     in
                  (uu____3831, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3840  ->
                            fun uu____3841  ->
                              match (uu____3840, uu____3841) with
                              | ((int_to_t1,x),(uu____3852,y)) ->
                                  int_as_bounded r int_to_t1 (x * y))))
                   in
                [uu____3822]  in
              uu____3776 :: uu____3812  in
            uu____3730 :: uu____3766))
     in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
  
let equality_ops : primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____3918)::(a1,uu____3920)::(a2,uu____3922)::[] ->
        let uu____3951 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____3951 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___165_3955 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_3955.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_3955.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_3955.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___166_3962 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_3962.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___166_3962.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_3962.FStar_Syntax_Syntax.vars)
                })
         | uu____3967 -> None)
    | (_typ,uu____3969)::uu____3970::(a1,uu____3972)::(a2,uu____3974)::[] ->
        let uu____4011 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____4011 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___165_4015 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_4015.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___165_4015.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_4015.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___166_4022 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_4022.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___166_4022.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_4022.FStar_Syntax_Syntax.vars)
                })
         | uu____4027 -> None)
    | uu____4028 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Syntax_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Syntax_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      interpretation = interp_prop
    }  in
  [propositional_equality; hetero_propositional_equality] 
let reduce_primops :
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____4038 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps)
         in
      if uu____4038
      then tm
      else
        (let uu____4040 = FStar_Syntax_Util.head_and_args tm  in
         match uu____4040 with
         | (head1,args) ->
             let uu____4066 =
               let uu____4067 = FStar_Syntax_Util.un_uinst head1  in
               uu____4067.FStar_Syntax_Syntax.n  in
             (match uu____4066 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4071 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps
                     in
                  (match uu____4071 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4083 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args
                             in
                          match uu____4083 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4086 -> tm))
  
let reduce_equality :
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___167_4093 = cfg  in
         {
           steps = [Primops];
           tcenv = (uu___167_4093.tcenv);
           delta_level = (uu___167_4093.delta_level);
           primitive_steps = equality_ops
         }) tm
  
let maybe_simplify :
  cfg ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      let steps = cfg.steps  in
      let w t =
        let uu___168_4115 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___168_4115.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___168_4115.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___168_4115.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4134 -> None  in
      let simplify arg = ((simp_t (fst arg)), arg)  in
      let tm1 = reduce_primops cfg tm  in
      let uu____4162 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps)
         in
      if uu____4162
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4165;
                     FStar_Syntax_Syntax.pos = uu____4166;
                     FStar_Syntax_Syntax.vars = uu____4167;_},uu____4168);
                FStar_Syntax_Syntax.tk = uu____4169;
                FStar_Syntax_Syntax.pos = uu____4170;
                FStar_Syntax_Syntax.vars = uu____4171;_},args)
             ->
             let uu____4191 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid
                in
             if uu____4191
             then
               let uu____4192 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               (match uu____4192 with
                | (Some (true ),uu____4225)::(uu____4226,(arg,uu____4228))::[]
                    -> arg
                | (uu____4269,(arg,uu____4271))::(Some (true ),uu____4272)::[]
                    -> arg
                | (Some (false ),uu____4313)::uu____4314::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4352::(Some (false ),uu____4353)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4391 -> tm1)
             else
               (let uu____4401 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid
                   in
                if uu____4401
                then
                  let uu____4402 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____4402 with
                  | (Some (true ),uu____4435)::uu____4436::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4474::(Some (true ),uu____4475)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4513)::(uu____4514,(arg,uu____4516))::[]
                      -> arg
                  | (uu____4557,(arg,uu____4559))::(Some (false ),uu____4560)::[]
                      -> arg
                  | uu____4601 -> tm1
                else
                  (let uu____4611 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid
                      in
                   if uu____4611
                   then
                     let uu____4612 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____4612 with
                     | uu____4645::(Some (true ),uu____4646)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4684)::uu____4685::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4723)::(uu____4724,(arg,uu____4726))::[]
                         -> arg
                     | (uu____4767,(p,uu____4769))::(uu____4770,(q,uu____4772))::[]
                         ->
                         let uu____4814 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____4814
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4816 -> tm1
                   else
                     (let uu____4826 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid
                         in
                      if uu____4826
                      then
                        let uu____4827 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____4827 with
                        | (Some (true ),uu____4860)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4884)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4908 -> tm1
                      else
                        (let uu____4918 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid
                            in
                         if uu____4918
                         then
                           match args with
                           | (t,uu____4920)::[] ->
                               let uu____4933 =
                                 let uu____4934 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____4934.FStar_Syntax_Syntax.n  in
                               (match uu____4933 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4937::[],body,uu____4939) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4955 -> tm1)
                                | uu____4957 -> tm1)
                           | (uu____4958,Some (FStar_Syntax_Syntax.Implicit
                              uu____4959))::(t,uu____4961)::[] ->
                               let uu____4988 =
                                 let uu____4989 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____4989.FStar_Syntax_Syntax.n  in
                               (match uu____4988 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4992::[],body,uu____4994) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5010 -> tm1)
                                | uu____5012 -> tm1)
                           | uu____5013 -> tm1
                         else
                           (let uu____5020 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid
                               in
                            if uu____5020
                            then
                              match args with
                              | (t,uu____5022)::[] ->
                                  let uu____5035 =
                                    let uu____5036 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____5036.FStar_Syntax_Syntax.n  in
                                  (match uu____5035 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5039::[],body,uu____5041) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5057 -> tm1)
                                   | uu____5059 -> tm1)
                              | (uu____5060,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5061))::
                                  (t,uu____5063)::[] ->
                                  let uu____5090 =
                                    let uu____5091 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____5091.FStar_Syntax_Syntax.n  in
                                  (match uu____5090 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5094::[],body,uu____5096) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5112 -> tm1)
                                   | uu____5114 -> tm1)
                              | uu____5115 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5123;
                FStar_Syntax_Syntax.pos = uu____5124;
                FStar_Syntax_Syntax.vars = uu____5125;_},args)
             ->
             let uu____5141 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid
                in
             if uu____5141
             then
               let uu____5142 =
                 FStar_All.pipe_right args (FStar_List.map simplify)  in
               (match uu____5142 with
                | (Some (true ),uu____5175)::(uu____5176,(arg,uu____5178))::[]
                    -> arg
                | (uu____5219,(arg,uu____5221))::(Some (true ),uu____5222)::[]
                    -> arg
                | (Some (false ),uu____5263)::uu____5264::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5302::(Some (false ),uu____5303)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5341 -> tm1)
             else
               (let uu____5351 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid
                   in
                if uu____5351
                then
                  let uu____5352 =
                    FStar_All.pipe_right args (FStar_List.map simplify)  in
                  match uu____5352 with
                  | (Some (true ),uu____5385)::uu____5386::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5424::(Some (true ),uu____5425)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5463)::(uu____5464,(arg,uu____5466))::[]
                      -> arg
                  | (uu____5507,(arg,uu____5509))::(Some (false ),uu____5510)::[]
                      -> arg
                  | uu____5551 -> tm1
                else
                  (let uu____5561 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid
                      in
                   if uu____5561
                   then
                     let uu____5562 =
                       FStar_All.pipe_right args (FStar_List.map simplify)
                        in
                     match uu____5562 with
                     | uu____5595::(Some (true ),uu____5596)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5634)::uu____5635::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5673)::(uu____5674,(arg,uu____5676))::[]
                         -> arg
                     | (uu____5717,(p,uu____5719))::(uu____5720,(q,uu____5722))::[]
                         ->
                         let uu____5764 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5764
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5766 -> tm1
                   else
                     (let uu____5776 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid
                         in
                      if uu____5776
                      then
                        let uu____5777 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        match uu____5777 with
                        | (Some (true ),uu____5810)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5834)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5858 -> tm1
                      else
                        (let uu____5868 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid
                            in
                         if uu____5868
                         then
                           match args with
                           | (t,uu____5870)::[] ->
                               let uu____5883 =
                                 let uu____5884 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____5884.FStar_Syntax_Syntax.n  in
                               (match uu____5883 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5887::[],body,uu____5889) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5905 -> tm1)
                                | uu____5907 -> tm1)
                           | (uu____5908,Some (FStar_Syntax_Syntax.Implicit
                              uu____5909))::(t,uu____5911)::[] ->
                               let uu____5938 =
                                 let uu____5939 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____5939.FStar_Syntax_Syntax.n  in
                               (match uu____5938 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5942::[],body,uu____5944) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5960 -> tm1)
                                | uu____5962 -> tm1)
                           | uu____5963 -> tm1
                         else
                           (let uu____5970 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid
                               in
                            if uu____5970
                            then
                              match args with
                              | (t,uu____5972)::[] ->
                                  let uu____5985 =
                                    let uu____5986 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____5986.FStar_Syntax_Syntax.n  in
                                  (match uu____5985 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5989::[],body,uu____5991) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6007 -> tm1)
                                   | uu____6009 -> tm1)
                              | (uu____6010,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6011))::
                                  (t,uu____6013)::[] ->
                                  let uu____6040 =
                                    let uu____6041 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6041.FStar_Syntax_Syntax.n  in
                                  (match uu____6040 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6044::[],body,uu____6046) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6062 -> tm1)
                                   | uu____6064 -> tm1)
                              | uu____6065 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6072 -> tm1)
  
let is_norm_request hd1 args =
  let uu____6087 =
    let uu____6091 =
      let uu____6092 = FStar_Syntax_Util.un_uinst hd1  in
      uu____6092.FStar_Syntax_Syntax.n  in
    (uu____6091, args)  in
  match uu____6087 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6097::uu____6098::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6101::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6103 -> false 
let get_norm_request args =
  match args with
  | uu____6122::(tm,uu____6124)::[] -> tm
  | (tm,uu____6134)::[] -> tm
  | uu____6139 -> failwith "Impossible" 
let is_reify_head : stack_elt Prims.list -> Prims.bool =
  fun uu___143_6146  ->
    match uu___143_6146 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6148;
           FStar_Syntax_Syntax.pos = uu____6149;
           FStar_Syntax_Syntax.vars = uu____6150;_},uu____6151,uu____6152))::uu____6153
        -> true
    | uu____6159 -> false
  
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack1  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t  in
          let firstn k l =
            if (FStar_List.length l) < k
            then (l, [])
            else FStar_Util.first_N k l  in
          log cfg
            (fun uu____6270  ->
               let uu____6271 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____6272 = FStar_Syntax_Print.term_to_string t1  in
               let uu____6273 =
                 let uu____6274 =
                   let uu____6276 = firstn (Prims.parse_int "4") stack1  in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6276  in
                 stack_to_string uu____6274  in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6271
                 uu____6272 uu____6273);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6288 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6303 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6312 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6313 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6314;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6315;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6320;
                 FStar_Syntax_Syntax.fv_delta = uu____6321;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6325;
                 FStar_Syntax_Syntax.fv_delta = uu____6326;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6327);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                 (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args  in
               let hd2 = closure_as_term cfg env hd1  in
               let t2 =
                 let uu___169_6360 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___169_6360.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___169_6360.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___169_6360.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6386 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm)
                    in
                 Prims.op_Negation uu____6386) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Syntax_Const.prims_lid))
               ->
               let tm = get_norm_request args  in
               let s =
                 [Reify;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 Primops]  in
               let cfg' =
                 let uu___170_6399 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___170_6399.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___170_6399.primitive_steps)
                 }  in
               let stack' = (Debug t1) ::
                 (Steps
                    ((cfg.steps), (cfg.primitive_steps), (cfg.delta_level)))
                 :: stack1  in
               norm cfg' env stack' tm
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6404;
                  FStar_Syntax_Syntax.pos = uu____6405;
                  FStar_Syntax_Syntax.vars = uu____6406;_},a1::a2::rest)
               ->
               let uu____6440 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____6440 with
                | (hd1,uu____6451) ->
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
                    (FStar_Const.Const_reflect uu____6506);
                  FStar_Syntax_Syntax.tk = uu____6507;
                  FStar_Syntax_Syntax.pos = uu____6508;
                  FStar_Syntax_Syntax.vars = uu____6509;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6532 = FStar_List.tl stack1  in
               norm cfg env uu____6532 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6535;
                  FStar_Syntax_Syntax.pos = uu____6536;
                  FStar_Syntax_Syntax.vars = uu____6537;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6560 = FStar_Syntax_Util.head_and_args t1  in
               (match uu____6560 with
                | (reify_head,uu____6571) ->
                    let a1 =
                      let uu____6587 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a)
                         in
                      FStar_Syntax_Subst.compress uu____6587  in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6590);
                            FStar_Syntax_Syntax.tk = uu____6591;
                            FStar_Syntax_Syntax.pos = uu____6592;
                            FStar_Syntax_Syntax.vars = uu____6593;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6618 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1  in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____6626 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack1 uu____6626
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6633 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses)
                  in
               if uu____6633
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6636 =
                      let uu____6640 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____6640, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____6636  in
                  let stack2 = us1 :: stack1  in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1  in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___144_6649  ->
                         match uu___144_6649 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l))
                  in
               let should_delta1 =
                 let uu____6652 =
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
                           FStar_Syntax_Const.false_lid))
                    in
                 if uu____6652 then false else should_delta  in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6656 = FStar_Syntax_Syntax.range_of_fv f  in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6656  in
                  let uu____6657 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  match uu____6657 with
                  | None  ->
                      (log cfg
                         (fun uu____6668  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6674  ->
                            let uu____6675 =
                              FStar_Syntax_Print.term_to_string t0  in
                            let uu____6676 =
                              FStar_Syntax_Print.term_to_string t2  in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6675 uu____6676);
                       (let t3 =
                          let uu____6678 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant))
                             in
                          if uu____6678
                          then t2
                          else
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid
                                 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                              t2
                           in
                        let n1 = FStar_List.length us  in
                        if n1 > (Prims.parse_int "0")
                        then
                          match stack1 with
                          | (UnivArgs (us',uu____6690))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env)
                                 in
                              norm cfg env1 stack2 t3
                          | uu____6703 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6704 ->
                              let uu____6705 =
                                let uu____6706 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6706
                                 in
                              failwith uu____6705
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6713 = lookup_bvar env x  in
               (match uu____6713 with
                | Univ uu____6714 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6729 = FStar_ST.read r  in
                      (match uu____6729 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6748  ->
                                 let uu____6749 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____6750 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6749
                                   uu____6750);
                            (let uu____6751 =
                               let uu____6752 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____6752.FStar_Syntax_Syntax.n  in
                             match uu____6751 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6755 ->
                                 norm cfg env2 stack1 t'
                             | uu____6765 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____6788)::uu____6789 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6794)::uu____6795 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6801,uu____6802))::stack_rest ->
                    (match c with
                     | Univ uu____6805 -> norm cfg (c :: env) stack_rest t1
                     | uu____6806 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6809::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6817  ->
                                         let uu____6818 = closure_to_string c
                                            in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6818);
                                    norm cfg (c :: env) stack_rest body)
                               | Some rc when
                                   ((FStar_Ident.lid_equals
                                       rc.FStar_Syntax_Syntax.residual_effect
                                       FStar_Syntax_Const.effect_Tot_lid)
                                      ||
                                      (FStar_Ident.lid_equals
                                         rc.FStar_Syntax_Syntax.residual_effect
                                         FStar_Syntax_Const.effect_GTot_lid))
                                     ||
                                     (FStar_All.pipe_right
                                        rc.FStar_Syntax_Syntax.residual_flags
                                        (FStar_Util.for_some
                                           (fun uu___145_6821  ->
                                              match uu___145_6821 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6822 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6824  ->
                                         let uu____6825 = closure_to_string c
                                            in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6825);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6826 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6828 ->
                                   let cfg1 =
                                     let uu___171_6831 = cfg  in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___171_6831.tcenv);
                                       delta_level =
                                         (uu___171_6831.delta_level);
                                       primitive_steps =
                                         (uu___171_6831.primitive_steps)
                                     }  in
                                   let uu____6832 =
                                     closure_as_term cfg1 env t1  in
                                   rebuild cfg1 env stack1 uu____6832)
                          | uu____6833::tl1 ->
                              (log cfg
                                 (fun uu____6843  ->
                                    let uu____6844 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6844);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___172_6863 = cfg  in
                       {
                         steps = s;
                         tcenv = (uu___172_6863.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____6876  ->
                          let uu____6877 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6877);
                     norm cfg env stack2 t1)
                | (Debug uu____6878)::uu____6879 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6881 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____6881
                    else
                      (let uu____6883 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____6883 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____6894 =
                                   let uu___173_6895 = rc  in
                                   let uu____6896 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                      in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_6895.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____6896;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_6895.FStar_Syntax_Syntax.residual_flags)
                                   }  in
                                 Some uu____6894
                             | uu____6902 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6911  -> Dummy :: env1) env)
                              in
                           (log cfg
                              (fun uu____6916  ->
                                 let uu____6917 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6917);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___174_6927 = cfg  in
                               let uu____6928 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___174_6927.steps);
                                 tcenv = (uu___174_6927.tcenv);
                                 delta_level = (uu___174_6927.delta_level);
                                 primitive_steps = uu____6928
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____6933)::uu____6934 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6938 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____6938
                    else
                      (let uu____6940 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____6940 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____6951 =
                                   let uu___173_6952 = rc  in
                                   let uu____6953 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                      in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_6952.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____6953;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_6952.FStar_Syntax_Syntax.residual_flags)
                                   }  in
                                 Some uu____6951
                             | uu____6959 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____6968  -> Dummy :: env1) env)
                              in
                           (log cfg
                              (fun uu____6973  ->
                                 let uu____6974 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____6974);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___174_6984 = cfg  in
                               let uu____6985 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___174_6984.steps);
                                 tcenv = (uu___174_6984.tcenv);
                                 delta_level = (uu___174_6984.delta_level);
                                 primitive_steps = uu____6985
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____6990)::uu____6991 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6997 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____6997
                    else
                      (let uu____6999 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____6999 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7010 =
                                   let uu___173_7011 = rc  in
                                   let uu____7012 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                      in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7011.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7012;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7011.FStar_Syntax_Syntax.residual_flags)
                                   }  in
                                 Some uu____7010
                             | uu____7018 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7027  -> Dummy :: env1) env)
                              in
                           (log cfg
                              (fun uu____7032  ->
                                 let uu____7033 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7033);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___174_7043 = cfg  in
                               let uu____7044 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___174_7043.steps);
                                 tcenv = (uu___174_7043.tcenv);
                                 delta_level = (uu___174_7043.delta_level);
                                 primitive_steps = uu____7044
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7049)::uu____7050 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7055 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____7055
                    else
                      (let uu____7057 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____7057 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7068 =
                                   let uu___173_7069 = rc  in
                                   let uu____7070 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                      in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7069.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7070;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7069.FStar_Syntax_Syntax.residual_flags)
                                   }  in
                                 Some uu____7068
                             | uu____7076 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7085  -> Dummy :: env1) env)
                              in
                           (log cfg
                              (fun uu____7090  ->
                                 let uu____7091 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7091);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___174_7101 = cfg  in
                               let uu____7102 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___174_7101.steps);
                                 tcenv = (uu___174_7101.tcenv);
                                 delta_level = (uu___174_7101.delta_level);
                                 primitive_steps = uu____7102
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7107)::uu____7108 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7116 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____7116
                    else
                      (let uu____7118 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____7118 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7129 =
                                   let uu___173_7130 = rc  in
                                   let uu____7131 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                      in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7130.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7131;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7130.FStar_Syntax_Syntax.residual_flags)
                                   }  in
                                 Some uu____7129
                             | uu____7137 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7146  -> Dummy :: env1) env)
                              in
                           (log cfg
                              (fun uu____7151  ->
                                 let uu____7152 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7152);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___174_7162 = cfg  in
                               let uu____7163 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___174_7162.steps);
                                 tcenv = (uu___174_7162.tcenv);
                                 delta_level = (uu___174_7162.delta_level);
                                 primitive_steps = uu____7163
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7168 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____7168
                    else
                      (let uu____7170 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____7170 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some rc ->
                                 let uu____7181 =
                                   let uu___173_7182 = rc  in
                                   let uu____7183 =
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                      in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (uu___173_7182.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu____7183;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (uu___173_7182.FStar_Syntax_Syntax.residual_flags)
                                   }  in
                                 Some uu____7181
                             | uu____7189 -> lopt  in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7198  -> Dummy :: env1) env)
                              in
                           (log cfg
                              (fun uu____7203  ->
                                 let uu____7204 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7204);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1  in
                             let cfg1 =
                               let uu___174_7214 = cfg  in
                               let uu____7215 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps
                                  in
                               {
                                 steps = (uu___174_7214.steps);
                                 tcenv = (uu___174_7214.tcenv);
                                 delta_level = (uu___174_7214.delta_level);
                                 primitive_steps = uu____7215
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack2 =
                 FStar_All.pipe_right stack1
                   (FStar_List.fold_right
                      (fun uu____7242  ->
                         fun stack2  ->
                           match uu____7242 with
                           | (a,aq) ->
                               let uu____7250 =
                                 let uu____7251 =
                                   let uu____7255 =
                                     let uu____7256 =
                                       let uu____7266 =
                                         FStar_Util.mk_ref None  in
                                       (env, a, uu____7266, false)  in
                                     Clos uu____7256  in
                                   (uu____7255, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____7251  in
                               uu____7250 :: stack2) args)
                  in
               (log cfg
                  (fun uu____7288  ->
                     let uu____7289 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7289);
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
                             ((let uu___175_7310 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___175_7310.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___175_7310.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack1 t2
                  | uu____7311 ->
                      let uu____7314 = closure_as_term cfg env t1  in
                      rebuild cfg env stack1 uu____7314)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____7317 = FStar_Syntax_Subst.open_term [(x, None)] f
                     in
                  match uu____7317 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1  in
                      let t2 =
                        let uu____7333 =
                          let uu____7334 =
                            let uu____7339 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___176_7340 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___176_7340.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___176_7340.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7339)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____7334  in
                        mk uu____7333 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7353 = closure_as_term cfg env t1  in
                 rebuild cfg env stack1 uu____7353
               else
                 (let uu____7355 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____7355 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7361 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7367  -> Dummy :: env1)
                               env)
                           in
                        norm_comp cfg uu____7361 c1  in
                      let t2 =
                        let uu____7374 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____7374 c2  in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7417)::uu____7418 -> norm cfg env stack1 t11
                | (Arg uu____7423)::uu____7424 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____7429;
                       FStar_Syntax_Syntax.pos = uu____7430;
                       FStar_Syntax_Syntax.vars = uu____7431;_},uu____7432,uu____7433))::uu____7434
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7440)::uu____7441 ->
                    norm cfg env stack1 t11
                | uu____7446 ->
                    let t12 = norm cfg env [] t11  in
                    (log cfg
                       (fun uu____7449  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____7462 = norm cfg env [] t2  in
                            FStar_Util.Inl uu____7462
                        | FStar_Util.Inr c ->
                            let uu____7470 = norm_comp cfg env c  in
                            FStar_Util.Inr uu____7470
                         in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env [])  in
                      let uu____7475 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack1 uu____7475)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1  in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____7526,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7527;
                              FStar_Syntax_Syntax.lbunivs = uu____7528;
                              FStar_Syntax_Syntax.lbtyp = uu____7529;
                              FStar_Syntax_Syntax.lbeff = uu____7530;
                              FStar_Syntax_Syntax.lbdef = uu____7531;_}::uu____7532),uu____7533)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____7559 =
                 (let uu____7560 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps)
                     in
                  Prims.op_Negation uu____7560) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7561 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)
                             in
                          Prims.op_Negation uu____7561)))
                  in
               if uu____7559
               then
                 let env1 =
                   let uu____7564 =
                     let uu____7565 =
                       let uu____7575 = FStar_Util.mk_ref None  in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7575,
                         false)
                        in
                     Clos uu____7565  in
                   uu____7564 :: env  in
                 norm cfg env1 stack1 body
               else
                 (let uu____7599 =
                    let uu____7602 =
                      let uu____7603 =
                        let uu____7604 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left
                           in
                        FStar_All.pipe_right uu____7604
                          FStar_Syntax_Syntax.mk_binder
                         in
                      [uu____7603]  in
                    FStar_Syntax_Subst.open_term uu____7602 body  in
                  match uu____7599 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___177_7610 = lb  in
                        let uu____7611 =
                          let uu____7614 =
                            let uu____7615 = FStar_List.hd bs  in
                            FStar_All.pipe_right uu____7615
                              FStar_Pervasives.fst
                             in
                          FStar_All.pipe_right uu____7614
                            (fun _0_41  -> FStar_Util.Inl _0_41)
                           in
                        let uu____7624 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                        let uu____7627 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7611;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___177_7610.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7624;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___177_7610.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7627
                        }  in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____7637  -> Dummy :: env1)
                             env)
                         in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____7653 = closure_as_term cfg env t1  in
               rebuild cfg env stack1 uu____7653
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7666 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7688  ->
                        match uu____7688 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____7727 =
                                let uu___178_7728 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___178_7728.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___178_7728.FStar_Syntax_Syntax.sort)
                                }  in
                              FStar_Syntax_Syntax.bv_to_tm uu____7727  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo = FStar_Util.mk_ref None  in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____7666 with
                | (rec_env,memos,uu____7788) ->
                    let uu____7803 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.write memo
                               (Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____7845 =
                               let uu____7846 =
                                 let uu____7856 = FStar_Util.mk_ref None  in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____7856, false)
                                  in
                               Clos uu____7846  in
                             uu____7845 :: env1) (snd lbs) env
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
                             FStar_Syntax_Syntax.tk = uu____7894;
                             FStar_Syntax_Syntax.pos = uu____7895;
                             FStar_Syntax_Syntax.vars = uu____7896;_},uu____7897,uu____7898))::uu____7899
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____7905 -> false  in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2  in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1  in
                      let cfg1 =
                        let uu____7912 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations)
                           in
                        if uu____7912
                        then
                          let uu___179_7913 = cfg  in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___179_7913.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___179_7913.primitive_steps)
                          }
                        else
                          (let uu___180_7915 = cfg  in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___180_7915.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___180_7915.primitive_steps)
                           })
                         in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____7917 =
                         let uu____7918 = FStar_Syntax_Subst.compress head1
                            in
                         uu____7918.FStar_Syntax_Syntax.n  in
                       match uu____7917 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____7932 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____7932 with
                            | (uu____7933,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____7937 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____7944 =
                                         let uu____7945 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____7945.FStar_Syntax_Syntax.n  in
                                       match uu____7944 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____7950,uu____7951))
                                           ->
                                           let uu____7960 =
                                             let uu____7961 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____7961.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____7960 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____7966,msrc,uu____7968))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____7977 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                Some uu____7977
                                            | uu____7978 -> None)
                                       | uu____7979 -> None  in
                                     let uu____7980 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____7980 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___181_7984 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___181_7984.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___181_7984.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___181_7984.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            }  in
                                          let uu____7985 =
                                            FStar_List.tl stack1  in
                                          let uu____7986 =
                                            let uu____7987 =
                                              let uu____7990 =
                                                let uu____7991 =
                                                  let uu____7999 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
                                                    uu____7999)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____7991
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7990
                                               in
                                            uu____7987 None
                                              head1.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env uu____7985 uu____7986
                                      | None  ->
                                          let uu____8016 =
                                            let uu____8017 = is_return body
                                               in
                                            match uu____8017 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8020;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8021;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8022;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8027 -> false  in
                                          if uu____8016
                                          then
                                            norm cfg env stack1
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let head2 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef
                                                in
                                             let body1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             let body_rc =
                                               {
                                                 FStar_Syntax_Syntax.residual_effect
                                                   = m1;
                                                 FStar_Syntax_Syntax.residual_typ
                                                   = (Some t2);
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               }  in
                                             let body2 =
                                               let uu____8050 =
                                                 let uu____8053 =
                                                   let uu____8054 =
                                                     let uu____8064 =
                                                       let uu____8066 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____8066]  in
                                                     (uu____8064, body1,
                                                       (Some body_rc))
                                                      in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8054
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8053
                                                  in
                                               uu____8050 None
                                                 body1.FStar_Syntax_Syntax.pos
                                                in
                                             let close1 =
                                               closure_as_term cfg env  in
                                             let bind_inst =
                                               let uu____8085 =
                                                 let uu____8086 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr
                                                    in
                                                 uu____8086.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____8085 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8092::uu____8093::[])
                                                   ->
                                                   let uu____8099 =
                                                     let uu____8102 =
                                                       let uu____8103 =
                                                         let uu____8108 =
                                                           let uu____8110 =
                                                             let uu____8111 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp
                                                                in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8111
                                                              in
                                                           let uu____8112 =
                                                             let uu____8114 =
                                                               let uu____8115
                                                                 = close1 t2
                                                                  in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8115
                                                                in
                                                             [uu____8114]  in
                                                           uu____8110 ::
                                                             uu____8112
                                                            in
                                                         (bind1, uu____8108)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8103
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8102
                                                      in
                                                   uu____8099 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8127 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects"
                                                in
                                             let reified =
                                               let uu____8133 =
                                                 let uu____8136 =
                                                   let uu____8137 =
                                                     let uu____8147 =
                                                       let uu____8149 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____8150 =
                                                         let uu____8152 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2
                                                            in
                                                         let uu____8153 =
                                                           let uu____8155 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           let uu____8156 =
                                                             let uu____8158 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2
                                                                in
                                                             let uu____8159 =
                                                               let uu____8161
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               let uu____8162
                                                                 =
                                                                 let uu____8164
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2
                                                                    in
                                                                 [uu____8164]
                                                                  in
                                                               uu____8161 ::
                                                                 uu____8162
                                                                in
                                                             uu____8158 ::
                                                               uu____8159
                                                              in
                                                           uu____8155 ::
                                                             uu____8156
                                                            in
                                                         uu____8152 ::
                                                           uu____8153
                                                          in
                                                       uu____8149 ::
                                                         uu____8150
                                                        in
                                                     (bind_inst, uu____8147)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8137
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8136
                                                  in
                                               uu____8133 None
                                                 t2.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____8176 =
                                               FStar_List.tl stack1  in
                                             norm cfg env uu____8176 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1
                              in
                           let uu____8194 = ed.FStar_Syntax_Syntax.bind_repr
                              in
                           (match uu____8194 with
                            | (uu____8195,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8218 =
                                        let uu____8219 =
                                          FStar_Syntax_Subst.compress t3  in
                                        uu____8219.FStar_Syntax_Syntax.n  in
                                      match uu____8218 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8225) -> t4
                                      | uu____8230 -> head2  in
                                    let uu____8231 =
                                      let uu____8232 =
                                        FStar_Syntax_Subst.compress t4  in
                                      uu____8232.FStar_Syntax_Syntax.n  in
                                    match uu____8231 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8237 -> None  in
                                  let uu____8238 = maybe_extract_fv head2  in
                                  match uu____8238 with
                                  | Some x when
                                      let uu____8244 =
                                        FStar_Syntax_Syntax.lid_of_fv x  in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8244
                                      ->
                                      let head3 = norm cfg env [] head2  in
                                      let action_unfolded =
                                        let uu____8248 =
                                          maybe_extract_fv head3  in
                                        match uu____8248 with
                                        | Some uu____8251 -> Some true
                                        | uu____8252 -> Some false  in
                                      (head3, action_unfolded)
                                  | uu____8255 -> (head2, None)  in
                                ((let is_arg_impure uu____8266 =
                                    match uu____8266 with
                                    | (e,q) ->
                                        let uu____8271 =
                                          let uu____8272 =
                                            FStar_Syntax_Subst.compress e  in
                                          uu____8272.FStar_Syntax_Syntax.n
                                           in
                                        (match uu____8271 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8287 -> false)
                                     in
                                  let uu____8288 =
                                    let uu____8289 =
                                      let uu____8293 =
                                        FStar_Syntax_Syntax.as_arg head_app
                                         in
                                      uu____8293 :: args  in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8289
                                     in
                                  if uu____8288
                                  then
                                    let uu____8296 =
                                      let uu____8297 =
                                        FStar_Syntax_Print.term_to_string
                                          head1
                                         in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8297
                                       in
                                    failwith uu____8296
                                  else ());
                                 (let uu____8299 =
                                    maybe_unfold_action head_app  in
                                  match uu____8299 with
                                  | (head_app1,found_action) ->
                                      let mk1 tm =
                                        FStar_Syntax_Syntax.mk tm None
                                          t2.FStar_Syntax_Syntax.pos
                                         in
                                      let body =
                                        mk1
                                          (FStar_Syntax_Syntax.Tm_app
                                             (head_app1, args))
                                         in
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
                                        | Some (true ) -> body  in
                                      let uu____8334 = FStar_List.tl stack1
                                         in
                                      norm cfg env uu____8334 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8348 = closure_as_term cfg env t'  in
                             reify_lift cfg.tcenv e msrc mtgt uu____8348  in
                           let uu____8349 = FStar_List.tl stack1  in
                           norm cfg env uu____8349 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____8432  ->
                                     match uu____8432 with
                                     | (pat,wopt,tm) ->
                                         let uu____8470 =
                                           FStar_Syntax_Util.mk_reify tm  in
                                         (pat, wopt, uu____8470)))
                              in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____8496 = FStar_List.tl stack1  in
                           norm cfg env uu____8496 tm
                       | uu____8497 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____8506;
                             FStar_Syntax_Syntax.pos = uu____8507;
                             FStar_Syntax_Syntax.vars = uu____8508;_},uu____8509,uu____8510))::uu____8511
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8517 -> false  in
                    if should_reify
                    then
                      let uu____8518 = FStar_List.tl stack1  in
                      let uu____8519 =
                        let uu____8520 = closure_as_term cfg env t2  in
                        reify_lift cfg.tcenv head1 m1 m' uu____8520  in
                      norm cfg env uu____8518 uu____8519
                    else
                      (let t3 = norm cfg env [] t2  in
                       let uu____8523 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations))
                          in
                       if uu____8523
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1  in
                         let cfg1 =
                           let uu___182_8529 = cfg  in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___182_8529.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___182_8529.primitive_steps)
                           }  in
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
                | uu____8531 ->
                    (match stack1 with
                     | uu____8532::uu____8533 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8537)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_alien (b,s) ->
                              norm cfg env
                                ((Meta (m, (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args  in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____8554 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1  in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____8564 =
                                 norm_pattern_args cfg env args  in
                               FStar_Syntax_Syntax.Meta_pattern uu____8564
                           | uu____8571 -> m  in
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
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
              let uu____8583 = ed.FStar_Syntax_Syntax.return_repr  in
              match uu____8583 with
              | (uu____8584,return_repr) ->
                  let return_inst =
                    let uu____8591 =
                      let uu____8592 =
                        FStar_Syntax_Subst.compress return_repr  in
                      uu____8592.FStar_Syntax_Syntax.n  in
                    match uu____8591 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8598::[])
                        ->
                        let uu____8604 =
                          let uu____8607 =
                            let uu____8608 =
                              let uu____8613 =
                                let uu____8615 =
                                  env.FStar_TypeChecker_Env.universe_of env t
                                   in
                                [uu____8615]  in
                              (return_tm, uu____8613)  in
                            FStar_Syntax_Syntax.Tm_uinst uu____8608  in
                          FStar_Syntax_Syntax.mk uu____8607  in
                        uu____8604 None e.FStar_Syntax_Syntax.pos
                    | uu____8627 ->
                        failwith "NIY : Reification of indexed effects"
                     in
                  let uu____8630 =
                    let uu____8633 =
                      let uu____8634 =
                        let uu____8644 =
                          let uu____8646 = FStar_Syntax_Syntax.as_arg t  in
                          let uu____8647 =
                            let uu____8649 = FStar_Syntax_Syntax.as_arg e  in
                            [uu____8649]  in
                          uu____8646 :: uu____8647  in
                        (return_inst, uu____8644)  in
                      FStar_Syntax_Syntax.Tm_app uu____8634  in
                    FStar_Syntax_Syntax.mk uu____8633  in
                  uu____8630 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8662 = FStar_TypeChecker_Env.monad_leq env msrc mtgt
                  in
               match uu____8662 with
               | None  ->
                   let uu____8664 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____8664
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8665;
                     FStar_TypeChecker_Env.mtarget = uu____8666;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8667;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8678;
                     FStar_TypeChecker_Env.mtarget = uu____8679;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8680;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____8698 = FStar_Syntax_Util.mk_reify e  in
                   lift t FStar_Syntax_Syntax.tun uu____8698)

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
                (fun uu____8728  ->
                   match uu____8728 with
                   | (a,imp) ->
                       let uu____8735 = norm cfg env [] a  in
                       (uu____8735, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp  in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___183_8750 = comp1  in
            let uu____8753 =
              let uu____8754 =
                let uu____8760 = norm cfg env [] t  in
                let uu____8761 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____8760, uu____8761)  in
              FStar_Syntax_Syntax.Total uu____8754  in
            {
              FStar_Syntax_Syntax.n = uu____8753;
              FStar_Syntax_Syntax.tk = (uu___183_8750.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_8750.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_8750.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___184_8776 = comp1  in
            let uu____8779 =
              let uu____8780 =
                let uu____8786 = norm cfg env [] t  in
                let uu____8787 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____8786, uu____8787)  in
              FStar_Syntax_Syntax.GTotal uu____8780  in
            {
              FStar_Syntax_Syntax.n = uu____8779;
              FStar_Syntax_Syntax.tk = (uu___184_8776.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___184_8776.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___184_8776.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____8818  ->
                      match uu____8818 with
                      | (a,i) ->
                          let uu____8825 = norm cfg env [] a  in
                          (uu____8825, i)))
               in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___146_8830  ->
                      match uu___146_8830 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____8834 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____8834
                      | f -> f))
               in
            let uu___185_8838 = comp1  in
            let uu____8841 =
              let uu____8842 =
                let uu___186_8843 = ct  in
                let uu____8844 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____8845 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____8848 = norm_args ct.FStar_Syntax_Syntax.effect_args
                   in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____8844;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___186_8843.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____8845;
                  FStar_Syntax_Syntax.effect_args = uu____8848;
                  FStar_Syntax_Syntax.flags = flags
                }  in
              FStar_Syntax_Syntax.Comp uu____8842  in
            {
              FStar_Syntax_Syntax.n = uu____8841;
              FStar_Syntax_Syntax.tk = (uu___185_8838.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___185_8838.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___185_8838.FStar_Syntax_Syntax.vars)
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
            (let uu___187_8865 = cfg  in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___187_8865.tcenv);
               delta_level = (uu___187_8865.delta_level);
               primitive_steps = (uu___187_8865.primitive_steps)
             }) env [] t
           in
        let non_info t =
          let uu____8870 = norm1 t  in
          FStar_Syntax_Util.non_informative uu____8870  in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____8873 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___188_8887 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___188_8887.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___188_8887.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_8887.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name
               in
            let uu____8897 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ)
               in
            if uu____8897
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___189_8902 = ct  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___189_8902.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___189_8902.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___189_8902.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___189_8902.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                       in
                    let uu___190_8904 = ct1  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___190_8904.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___190_8904.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___190_8904.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___190_8904.FStar_Syntax_Syntax.flags)
                    }
                 in
              let uu___191_8905 = c  in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___191_8905.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___191_8905.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___191_8905.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____8911 -> c

and norm_binder :
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____8914  ->
        match uu____8914 with
        | (x,imp) ->
            let uu____8917 =
              let uu___192_8918 = x  in
              let uu____8919 = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___192_8918.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___192_8918.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____8919
              }  in
            (uu____8917, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____8925 =
          FStar_List.fold_left
            (fun uu____8932  ->
               fun b  ->
                 match uu____8932 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs
           in
        match uu____8925 with | (nbs,uu____8949) -> FStar_List.rev nbs

and norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp option ->
        FStar_Syntax_Syntax.residual_comp option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____8960 =
              let uu___193_8961 = rc  in
              let uu____8962 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___193_8961.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____8962;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___193_8961.FStar_Syntax_Syntax.residual_flags)
              }  in
            Some uu____8960
        | uu____8968 -> lopt

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
              ((let uu____8978 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms")
                   in
                if uu____8978
                then
                  let uu____8979 = FStar_Syntax_Print.term_to_string tm  in
                  let uu____8980 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____8979
                    uu____8980
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___194_8991 = cfg  in
                 {
                   steps = s;
                   tcenv = (uu___194_8991.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r  in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9011  ->
                    let uu____9012 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9012);
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
              let uu____9043 =
                let uu___195_9044 = FStar_Syntax_Util.abs bs1 t lopt1  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___195_9044.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___195_9044.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___195_9044.FStar_Syntax_Syntax.vars)
                }  in
              rebuild cfg env stack2 uu____9043
          | (Arg (Univ uu____9049,uu____9050,uu____9051))::uu____9052 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9054,uu____9055))::uu____9056 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us  in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9068),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9084  ->
                    let uu____9085 = FStar_Syntax_Print.term_to_string tm  in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9085);
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
                 (let uu____9096 = FStar_ST.read m  in
                  match uu____9096 with
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
                  | Some (uu____9122,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r  in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r
                 in
              let uu____9144 = maybe_simplify cfg t1  in
              rebuild cfg env stack2 uu____9144
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9151  ->
                    let uu____9152 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9152);
               (let scrutinee = t  in
                let norm_and_rebuild_match uu____9157 =
                  log cfg
                    (fun uu____9159  ->
                       let uu____9160 =
                         FStar_Syntax_Print.term_to_string scrutinee  in
                       let uu____9161 =
                         let uu____9162 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9169  ->
                                   match uu____9169 with
                                   | (p,uu____9175,uu____9176) ->
                                       FStar_Syntax_Print.pat_to_string p))
                            in
                         FStar_All.pipe_right uu____9162
                           (FStar_String.concat "\n\t")
                          in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9160 uu____9161);
                  (let whnf = FStar_List.contains WHNF cfg.steps  in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___147_9186  ->
                               match uu___147_9186 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9187 -> false))
                        in
                     let steps' =
                       let uu____9190 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations)
                          in
                       if uu____9190
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta]  in
                     let uu___196_9193 = cfg  in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___196_9193.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___196_9193.primitive_steps)
                     }  in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1  in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9227 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9243 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9277  ->
                                   fun uu____9278  ->
                                     match (uu____9277, uu____9278) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9343 = norm_pat env3 p1
                                            in
                                         (match uu____9343 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2))
                            in
                         (match uu____9243 with
                          | (pats1,env3) ->
                              ((let uu___197_9409 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___197_9409.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___197_9409.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___198_9423 = x  in
                           let uu____9424 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___198_9423.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___198_9423.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9424
                           }  in
                         ((let uu___199_9430 = p  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___199_9430.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___199_9430.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___200_9435 = x  in
                           let uu____9436 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___200_9435.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___200_9435.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9436
                           }  in
                         ((let uu___201_9442 = p  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___201_9442.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___201_9442.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___202_9452 = x  in
                           let uu____9453 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___202_9452.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___202_9452.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9453
                           }  in
                         let t2 = norm_or_whnf env2 t1  in
                         ((let uu___203_9460 = p  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___203_9460.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___203_9460.FStar_Syntax_Syntax.p)
                           }), env2)
                      in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____9464 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9467 =
                                   FStar_Syntax_Subst.open_branch branch1  in
                                 match uu____9467 with
                                 | (p,wopt,e) ->
                                     let uu____9485 = norm_pat env1 p  in
                                     (match uu____9485 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____9509 =
                                                  norm_or_whnf env2 w  in
                                                Some uu____9509
                                             in
                                          let e1 = norm_or_whnf env2 e  in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1))))
                      in
                   let uu____9514 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r
                      in
                   rebuild cfg env1 stack2 uu____9514)
                   in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9524) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9529 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9530;
                        FStar_Syntax_Syntax.fv_delta = uu____9531;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9535;
                        FStar_Syntax_Syntax.fv_delta = uu____9536;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9537);_}
                      -> true
                  | uu____9544 -> false  in
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
                let rec matches_pat scrutinee_orig p =
                  let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                     in
                  let uu____9643 = FStar_Syntax_Util.head_and_args scrutinee1
                     in
                  match uu____9643 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____9675 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____9677 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____9679 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____9691 ->
                                let uu____9692 =
                                  let uu____9693 = is_cons head1  in
                                  Prims.op_Negation uu____9693  in
                                FStar_Util.Inr uu____9692)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____9707 =
                             let uu____9708 =
                               FStar_Syntax_Util.un_uinst head1  in
                             uu____9708.FStar_Syntax_Syntax.n  in
                           (match uu____9707 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____9715 ->
                                let uu____9716 =
                                  let uu____9717 = is_cons head1  in
                                  Prims.op_Negation uu____9717  in
                                FStar_Util.Inr uu____9716))
                
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____9751)::rest_a,(p1,uu____9754)::rest_p) ->
                      let uu____9782 = matches_pat t1 p1  in
                      (match uu____9782 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____9796 -> FStar_Util.Inr false
                 in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____9867 = matches_pat scrutinee1 p1  in
                      (match uu____9867 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____9877  ->
                                 let uu____9878 =
                                   FStar_Syntax_Print.pat_to_string p1  in
                                 let uu____9879 =
                                   let uu____9880 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s
                                      in
                                   FStar_All.pipe_right uu____9880
                                     (FStar_String.concat "; ")
                                    in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____9878 uu____9879);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____9889 =
                                        let uu____9890 =
                                          let uu____9900 =
                                            FStar_Util.mk_ref (Some ([], t1))
                                             in
                                          ([], t1, uu____9900, false)  in
                                        Clos uu____9890  in
                                      uu____9889 :: env2) env1 s
                                in
                             let uu____9923 = guard_when_clause wopt b rest
                                in
                             norm cfg env2 stack2 uu____9923)))
                   in
                let uu____9924 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota))
                   in
                if uu____9924
                then norm_and_rebuild_match ()
                else matches scrutinee branches))

let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___148_9938  ->
                match uu___148_9938 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____9941 -> []))
         in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____9945 -> d  in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps
      }
  
let normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e  in
          let c1 =
            let uu___204_9965 = config s e  in
            {
              steps = (uu___204_9965.steps);
              tcenv = (uu___204_9965.tcenv);
              delta_level = (uu___204_9965.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps)
            }  in
          norm c1 [] [] t
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____9984 = config s e  in norm_comp uu____9984 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____9991 = config [] env  in norm_universe uu____9991 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____9998 = config [] env  in ghost_to_pure_aux uu____9998 [] c
  
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
        let uu____10010 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____10010  in
      let uu____10011 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____10011
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___205_10013 = lc  in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___205_10013.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___205_10013.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10014  ->
                    let uu____10015 = lc.FStar_Syntax_Syntax.comp ()  in
                    ghost_to_pure env uu____10015))
            }
        | None  -> lc
      else lc
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____10028 = FStar_Util.message_of_exn e  in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10028);
             t)
         in
      FStar_Syntax_Print.term_to_string t1
  
let comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10037 = config [AllowUnboundUniverses] env  in
          norm_comp uu____10037 [] c
        with
        | e ->
            ((let uu____10041 = FStar_Util.message_of_exn e  in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10041);
             c)
         in
      FStar_Syntax_Print.comp_to_string c1
  
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
                   let uu____10078 =
                     let uu____10079 =
                       let uu____10084 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____10084)  in
                     FStar_Syntax_Syntax.Tm_refine uu____10079  in
                   mk uu____10078 t01.FStar_Syntax_Syntax.pos
               | uu____10089 -> t2)
          | uu____10090 -> t2  in
        aux t
  
let unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize [WHNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta]
        env t
  
let reduce_uvar_solutions :
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
  
let eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____10112 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____10112 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10128 ->
                 let uu____10132 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____10132 with
                  | (actuals,uu____10138,uu____10139) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10151 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____10151 with
                         | (binders,args) ->
                             let uu____10161 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____10161
                               (Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10170 =
        let uu____10174 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
        (uu____10174, (t.FStar_Syntax_Syntax.n))  in
      match uu____10170 with
      | (Some sort,uu____10181) ->
          let uu____10183 = mk sort t.FStar_Syntax_Syntax.pos  in
          eta_expand_with_type env t uu____10183
      | (uu____10184,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10188 ->
          let uu____10192 = FStar_Syntax_Util.head_and_args t  in
          (match uu____10192 with
           | (head1,args) ->
               let uu____10218 =
                 let uu____10219 = FStar_Syntax_Subst.compress head1  in
                 uu____10219.FStar_Syntax_Syntax.n  in
               (match uu____10218 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10222,thead) ->
                    let uu____10236 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____10236 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____10267 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___210_10271 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___210_10271.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___210_10271.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___210_10271.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___210_10271.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___210_10271.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___210_10271.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___210_10271.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___210_10271.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___210_10271.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___210_10271.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___210_10271.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___210_10271.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___210_10271.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___210_10271.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___210_10271.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___210_10271.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___210_10271.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___210_10271.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___210_10271.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___210_10271.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___210_10271.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___210_10271.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___210_10271.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___210_10271.FStar_TypeChecker_Env.is_native_tactic)
                                 }) t
                               in
                            match uu____10267 with
                            | (uu____10272,ty,uu____10274) ->
                                eta_expand_with_type env t ty))
                | uu____10275 ->
                    let uu____10276 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___211_10280 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___211_10280.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___211_10280.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___211_10280.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___211_10280.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___211_10280.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___211_10280.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___211_10280.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___211_10280.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___211_10280.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___211_10280.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___211_10280.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___211_10280.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___211_10280.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___211_10280.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___211_10280.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___211_10280.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___211_10280.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___211_10280.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___211_10280.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___211_10280.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___211_10280.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___211_10280.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___211_10280.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___211_10280.FStar_TypeChecker_Env.is_native_tactic)
                         }) t
                       in
                    (match uu____10276 with
                     | (uu____10281,ty,uu____10283) ->
                         eta_expand_with_type env t ty)))
  