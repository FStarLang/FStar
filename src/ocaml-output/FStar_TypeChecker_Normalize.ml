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
type closure =
  | Clos of (closure Prims.list* FStar_Syntax_Syntax.term* (closure
  Prims.list* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo*
  Prims.bool)
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____120 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____159 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____170 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___123_174  ->
    match uu___123_174 with
    | Clos (uu____175,t,uu____177,uu____178) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____189 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;}
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
  | Steps of (steps* FStar_TypeChecker_Env.delta_level Prims.list)
  | Debug of FStar_Syntax_Syntax.term
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____290 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____314 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____338 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____365 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____394 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either Prims.option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____433 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____456 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____478 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____505 -> false
let __proj__Steps__item___0:
  stack_elt -> (steps* FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____526 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____574 = FStar_ST.read r in
  match uu____574 with
  | Some uu____579 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____588 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____588 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___124_593  ->
    match uu___124_593 with
    | Arg (c,uu____595,uu____596) ->
        let uu____597 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____597
    | MemoLazy uu____598 -> "MemoLazy"
    | Abs (uu____602,bs,uu____604,uu____605,uu____606) ->
        let uu____613 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____613
    | UnivArgs uu____618 -> "UnivArgs"
    | Match uu____622 -> "Match"
    | App (t,uu____627,uu____628) ->
        let uu____629 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____629
    | Meta (m,uu____631) -> "Meta"
    | Let uu____632 -> "Let"
    | Steps (s,uu____638) -> "Steps"
    | Debug t ->
        let uu____642 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____642
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____648 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____648 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____662 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      match uu____662 with | true  -> f () | uu____663 -> ()
let is_empty uu___125_671 =
  match uu___125_671 with | [] -> true | uu____673 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____691 ->
      let uu____692 =
        let uu____693 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____693 in
      failwith uu____692
let comp_to_comp_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ
  =
  fun env  ->
    fun c  ->
      let c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,None ) ->
            let u = env.FStar_TypeChecker_Env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (Some u)
        | FStar_Syntax_Syntax.GTotal (t,None ) ->
            let u = env.FStar_TypeChecker_Env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (Some u)
        | uu____715 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c
let rec unfold_effect_abbrev:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ
  =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____723 =
        FStar_TypeChecker_Env.lookup_effect_abbrev env
          c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name in
      match uu____723 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____733 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____733 with
           | (binders,cdef) ->
               ((match (FStar_List.length binders) <>
                         ((FStar_List.length
                             c.FStar_Syntax_Syntax.effect_args)
                            + (Prims.parse_int "1"))
                 with
                 | true  ->
                     let uu____750 =
                       let uu____751 =
                         let uu____754 =
                           let uu____755 =
                             FStar_Util.string_of_int
                               (FStar_List.length binders) in
                           let uu____761 =
                             FStar_Util.string_of_int
                               ((FStar_List.length
                                   c.FStar_Syntax_Syntax.effect_args)
                                  + (Prims.parse_int "1")) in
                           let uu____769 =
                             let uu____770 = FStar_Syntax_Syntax.mk_Comp c in
                             FStar_Syntax_Print.comp_to_string uu____770 in
                           FStar_Util.format3
                             "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                             uu____755 uu____761 uu____769 in
                         (uu____754, (comp.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____751 in
                     Prims.raise uu____750
                 | uu____771 -> ());
                (let inst =
                   let uu____774 =
                     let uu____780 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____780 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____787  ->
                        fun uu____788  ->
                          match (uu____787, uu____788) with
                          | ((x,uu____802),(t,uu____804)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders
                     uu____774 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef in
                 let c =
                   let uu____819 =
                     let uu___135_820 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___135_820.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___135_820.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___135_820.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___135_820.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____819 FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c)))
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun l  ->
    match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid with
    | true  -> Some FStar_Syntax_Const.effect_Pure_lid
    | uu____826 ->
        (match FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid
         with
         | true  -> Some FStar_Syntax_Const.effect_Tot_lid
         | uu____828 ->
             (match FStar_Ident.lid_equals l
                      FStar_Syntax_Const.effect_GHOST_lid
              with
              | true  -> Some FStar_Syntax_Const.effect_PURE_lid
              | uu____830 -> None))
let norm_universe:
  cfg ->
    closure Prims.list ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____851 =
            FStar_List.fold_left
              (fun uu____860  ->
                 fun u  ->
                   match uu____860 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____875 = FStar_Syntax_Util.univ_kernel u in
                       (match uu____875 with
                        | (k_u,n) ->
                            let uu____884 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            (match uu____884 with
                             | true  -> (cur_kernel, u, out)
                             | uu____890 -> (k_u, u, (cur_max :: out)))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us in
          match uu____851 with
          | (uu____894,u,out) -> FStar_List.rev (u :: out) in
        let rec aux u =
          let u = FStar_Syntax_Subst.compress_univ u in
          match u with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____910 = FStar_List.nth env x in
                 match uu____910 with
                 | Univ u -> aux u
                 | Dummy  -> [u]
                 | uu____913 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____917 ->
                   let uu____918 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   (match uu____918 with
                    | true  -> [FStar_Syntax_Syntax.U_unknown]
                    | uu____920 -> failwith "Universe variable not found"))
          | FStar_Syntax_Syntax.U_zero 
            |FStar_Syntax_Syntax.U_unif _
             |FStar_Syntax_Syntax.U_name _|FStar_Syntax_Syntax.U_unknown  ->
              [u]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us =
                let uu____928 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____928 norm_univs in
              (match us with
               | u_k::hd::rest ->
                   let rest = hd :: rest in
                   let uu____939 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____939 with
                    | (FStar_Syntax_Syntax.U_zero ,n) ->
                        let uu____944 =
                          FStar_All.pipe_right rest
                            (FStar_List.for_all
                               (fun u  ->
                                  let uu____947 =
                                    FStar_Syntax_Util.univ_kernel u in
                                  match uu____947 with
                                  | (uu____950,m) -> n <= m)) in
                        (match uu____944 with
                         | true  -> rest
                         | uu____953 -> us)
                    | uu____954 -> us)
               | uu____957 -> us)
          | FStar_Syntax_Syntax.U_succ u ->
              let uu____960 = aux u in
              FStar_List.map (fun _0_33  -> FStar_Syntax_Syntax.U_succ _0_33)
                uu____960 in
        let uu____962 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        match uu____962 with
        | true  -> FStar_Syntax_Syntax.U_unknown
        | uu____963 ->
            let uu____964 = aux u in
            (match uu____964 with
             | []|(FStar_Syntax_Syntax.U_zero )::[] ->
                 FStar_Syntax_Syntax.U_zero
             | (FStar_Syntax_Syntax.U_zero )::u::[] -> u
             | (FStar_Syntax_Syntax.U_zero )::us ->
                 FStar_Syntax_Syntax.U_max us
             | u::[] -> u
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
          (fun uu____1061  ->
             let uu____1062 = FStar_Syntax_Print.tag_of_term t in
             let uu____1063 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1062
               uu____1063);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1064 ->
             let t = FStar_Syntax_Subst.compress t in
             (match t.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1067 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown 
                |FStar_Syntax_Syntax.Tm_constant _
                 |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _
                  -> t
              | FStar_Syntax_Syntax.Tm_uvar uu____1091 -> t
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1101 =
                    let uu____1102 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1102 in
                  mk uu____1101 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
                  let uu____1109 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t uu____1109
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1111 = lookup_bvar env x in
                  (match uu____1111 with
                   | Univ uu____1112 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t
                   | Clos (env,t0,r,uu____1116) -> closure_as_term cfg env t0)
              | FStar_Syntax_Syntax.Tm_app (head,args) ->
                  let head = closure_as_term_delayed cfg env head in
                  let args = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head, args))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1184 = closures_as_binders_delayed cfg env bs in
                  (match uu____1184 with
                   | (bs,env) ->
                       let body = closure_as_term_delayed cfg env body in
                       let uu____1204 =
                         let uu____1205 =
                           let uu____1220 = close_lcomp_opt cfg env lopt in
                           (bs, body, uu____1220) in
                         FStar_Syntax_Syntax.Tm_abs uu____1205 in
                       mk uu____1204 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1250 = closures_as_binders_delayed cfg env bs in
                  (match uu____1250 with
                   | (bs,env) ->
                       let c = close_comp cfg env c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                         t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1281 =
                    let uu____1288 =
                      let uu____1292 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1292] in
                    closures_as_binders_delayed cfg env uu____1288 in
                  (match uu____1281 with
                   | (x,env) ->
                       let phi = closure_as_term_delayed cfg env phi in
                       let uu____1306 =
                         let uu____1307 =
                           let uu____1312 =
                             let uu____1313 = FStar_List.hd x in
                             FStar_All.pipe_right uu____1313 Prims.fst in
                           (uu____1312, phi) in
                         FStar_Syntax_Syntax.Tm_refine uu____1307 in
                       mk uu____1306 t.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,lopt)
                  ->
                  let uu____1343 =
                    let uu____1344 =
                      let uu____1357 = closure_as_term_delayed cfg env t1 in
                      let uu____1360 =
                        let uu____1367 = closure_as_term_delayed cfg env t2 in
                        FStar_All.pipe_left
                          (fun _0_34  -> FStar_Util.Inl _0_34) uu____1367 in
                      (uu____1357, uu____1360, lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1344 in
                  mk uu____1343 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,lopt) ->
                  let uu____1412 =
                    let uu____1413 =
                      let uu____1426 = closure_as_term_delayed cfg env t1 in
                      let uu____1429 =
                        let uu____1436 = close_comp cfg env c in
                        FStar_All.pipe_left
                          (fun _0_35  -> FStar_Util.Inr _0_35) uu____1436 in
                      (uu____1426, uu____1429, lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1413 in
                  mk uu____1412 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1472 =
                    let uu____1473 =
                      let uu____1478 = closure_as_term_delayed cfg env t' in
                      let uu____1481 =
                        let uu____1482 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1482 in
                      (uu____1478, uu____1481) in
                    FStar_Syntax_Syntax.Tm_meta uu____1473 in
                  mk uu____1472 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1524 =
                    let uu____1525 =
                      let uu____1530 = closure_as_term_delayed cfg env t' in
                      let uu____1533 =
                        let uu____1534 =
                          let uu____1539 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1539) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1534 in
                      (uu____1530, uu____1533) in
                    FStar_Syntax_Syntax.Tm_meta uu____1525 in
                  mk uu____1524 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1558 =
                    let uu____1559 =
                      let uu____1564 = closure_as_term_delayed cfg env t' in
                      let uu____1567 =
                        let uu____1568 =
                          let uu____1574 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1574) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1568 in
                      (uu____1564, uu____1567) in
                    FStar_Syntax_Syntax.Tm_meta uu____1559 in
                  mk uu____1558 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1587 =
                    let uu____1588 =
                      let uu____1593 = closure_as_term_delayed cfg env t' in
                      (uu____1593, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1588 in
                  mk uu____1587 t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env =
                    FStar_List.fold_left
                      (fun env  -> fun uu____1614  -> Dummy :: env) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef in
                  let body =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1625 -> body
                    | FStar_Util.Inl uu____1626 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb =
                    let uu___138_1628 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___138_1628.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___138_1628.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___138_1628.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1635,lbs),body) ->
                  let norm_one_lb env lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1659  -> fun env  -> Dummy :: env)
                        lb.FStar_Syntax_Syntax.lbunivs env in
                    let env =
                      let uu____1664 = FStar_Syntax_Syntax.is_top_level lbs in
                      match uu____1664 with
                      | true  -> env_univs
                      | uu____1666 ->
                          FStar_List.fold_right
                            (fun uu____1668  -> fun env  -> Dummy :: env) lbs
                            env_univs in
                    let uu___139_1671 = lb in
                    let uu____1672 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1675 =
                      closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___139_1671.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___139_1671.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1672;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___139_1671.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1675
                    } in
                  let lbs =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1686  -> fun env  -> Dummy :: env) lbs env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                    t.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head,branches) ->
                  let head = closure_as_term cfg env head in
                  let norm_one_branch env uu____1741 =
                    match uu____1741 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1787 ->
                              (p, env)
                          | FStar_Syntax_Syntax.Pat_disj [] ->
                              failwith "Impossible"
                          | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                              let uu____1807 = norm_pat env hd in
                              (match uu____1807 with
                               | (hd,env') ->
                                   let tl =
                                     FStar_All.pipe_right tl
                                       (FStar_List.map
                                          (fun p  ->
                                             let uu____1843 = norm_pat env p in
                                             Prims.fst uu____1843)) in
                                   ((let uu___140_1855 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_disj (hd ::
                                            tl));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___140_1855.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___140_1855.FStar_Syntax_Syntax.p)
                                     }), env'))
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1872 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1906  ->
                                        fun uu____1907  ->
                                          match (uu____1906, uu____1907) with
                                          | ((pats,env),(p,b)) ->
                                              let uu____1972 = norm_pat env p in
                                              (match uu____1972 with
                                               | (p,env) ->
                                                   (((p, b) :: pats), env)))
                                     ([], env)) in
                              (match uu____1872 with
                               | (pats,env) ->
                                   ((let uu___141_2038 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___141_2038.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___141_2038.FStar_Syntax_Syntax.p)
                                     }), env))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x =
                                let uu___142_2052 = x in
                                let uu____2053 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___142_2052.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___142_2052.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2053
                                } in
                              ((let uu___143_2059 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___143_2059.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___143_2059.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x =
                                let uu___144_2064 = x in
                                let uu____2065 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___144_2064.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___144_2064.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2065
                                } in
                              ((let uu___145_2071 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___145_2071.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___145_2071.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                              let x =
                                let uu___146_2081 = x in
                                let uu____2082 =
                                  closure_as_term cfg env
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___146_2081.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___146_2081.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2082
                                } in
                              let t = closure_as_term cfg env t in
                              ((let uu___147_2089 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___147_2089.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___147_2089.FStar_Syntax_Syntax.p)
                                }), env) in
                        let uu____2092 = norm_pat env pat in
                        (match uu____2092 with
                         | (pat,env) ->
                             let w_opt =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2116 = closure_as_term cfg env w in
                                   Some uu____2116 in
                             let tm = closure_as_term cfg env tm in
                             (pat, w_opt, tm)) in
                  let uu____2121 =
                    let uu____2122 =
                      let uu____2138 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head, uu____2138) in
                    FStar_Syntax_Syntax.Tm_match uu____2122 in
                  mk uu____2121 t.FStar_Syntax_Syntax.pos))
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
        | uu____2191 -> closure_as_term cfg env t
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
        | uu____2207 ->
            FStar_List.map
              (fun uu____2217  ->
                 match uu____2217 with
                 | (x,imp) ->
                     let uu____2232 = closure_as_term_delayed cfg env x in
                     (uu____2232, imp)) args
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
        let uu____2244 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2268  ->
                  fun uu____2269  ->
                    match (uu____2268, uu____2269) with
                    | ((env,out),(b,imp)) ->
                        let b =
                          let uu___148_2313 = b in
                          let uu____2314 =
                            closure_as_term_delayed cfg env
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___148_2313.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___148_2313.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2314
                          } in
                        let env = Dummy :: env in (env, ((b, imp) :: out)))
               (env, [])) in
        match uu____2244 with | (env,bs) -> ((FStar_List.rev bs), env)
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
        | uu____2361 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2373 = closure_as_term_delayed cfg env t in
                 let uu____2374 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2373 uu____2374
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2384 = closure_as_term_delayed cfg env t in
                 let uu____2385 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2384 uu____2385
             | FStar_Syntax_Syntax.Comp c ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c.FStar_Syntax_Syntax.effect_args in
                 let flags =
                   FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___126_2401  ->
                           match uu___126_2401 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2405 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2405
                           | f -> f)) in
                 let uu____2409 =
                   let uu___149_2410 = c in
                   let uu____2411 =
                     FStar_List.map (norm_universe cfg env)
                       c.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2411;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___149_2410.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2409)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___127_2415  ->
            match uu___127_2415 with
            | FStar_Syntax_Syntax.DECREASES uu____2416 -> false
            | uu____2419 -> true))
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
            let uu____2447 = FStar_Syntax_Util.is_total_lcomp lc in
            (match uu____2447 with
             | true  ->
                 Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
             | uu____2463 ->
                 let uu____2464 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
                 (match uu____2464 with
                  | true  ->
                      Some
                        (FStar_Util.Inr
                           (FStar_Syntax_Const.effect_GTot_lid, flags))
                  | uu____2480 ->
                      Some
                        (FStar_Util.Inr
                           ((lc.FStar_Syntax_Syntax.eff_name), flags))))
        | uu____2490 -> lopt
let arith_ops:
  (FStar_Ident.lident* (Prims.int -> Prims.int -> FStar_Const.sconst))
    Prims.list
  =
  let int_as_const i =
    let uu____2508 =
      let uu____2514 = FStar_Util.string_of_int i in (uu____2514, None) in
    FStar_Const.Const_int uu____2508 in
  let bool_as_const b = FStar_Const.Const_bool b in
  let uu____2524 =
    let uu____2532 =
      FStar_List.map
        (fun m  ->
           let uu____2549 =
             let uu____2556 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
             (uu____2556, (fun x  -> fun y  -> int_as_const (x + y))) in
           let uu____2563 =
             let uu____2571 =
               let uu____2578 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
               (uu____2578, (fun x  -> fun y  -> int_as_const (x - y))) in
             let uu____2585 =
               let uu____2593 =
                 let uu____2600 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                 (uu____2600, (fun x  -> fun y  -> int_as_const (x * y))) in
               [uu____2593] in
             uu____2571 :: uu____2585 in
           uu____2549 :: uu____2563)
        ["Int8";
        "UInt8";
        "Int16";
        "UInt16";
        "Int32";
        "UInt32";
        "Int64";
        "UInt64";
        "UInt128"] in
    FStar_List.flatten uu____2532 in
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
      ((fun x  -> fun y  -> int_as_const (x mod y))))] uu____2524
let un_ops:
  (FStar_Ident.lident*
    (Prims.string ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax))
    Prims.list
  =
  let mk x = mk x FStar_Range.dummyRange in
  let name x =
    let uu____2795 =
      let uu____2796 =
        let uu____2797 = FStar_Syntax_Const.p2l x in
        FStar_Syntax_Syntax.lid_as_fv uu____2797
          FStar_Syntax_Syntax.Delta_constant None in
      FStar_Syntax_Syntax.Tm_fvar uu____2796 in
    mk uu____2795 in
  let ctor x =
    let uu____2806 =
      let uu____2807 =
        let uu____2808 = FStar_Syntax_Const.p2l x in
        FStar_Syntax_Syntax.lid_as_fv uu____2808
          FStar_Syntax_Syntax.Delta_constant
          (Some FStar_Syntax_Syntax.Data_ctor) in
      FStar_Syntax_Syntax.Tm_fvar uu____2807 in
    mk uu____2806 in
  let uu____2809 =
    let uu____2816 =
      FStar_Syntax_Const.p2l ["FStar"; "String"; "list_of_string"] in
    (uu____2816,
      (fun s  ->
         let uu____2822 = FStar_String.list_of_string s in
         let uu____2824 =
           let uu____2827 =
             let uu____2828 =
               let uu____2838 =
                 let uu____2839 = ctor ["Prims"; "Nil"] in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2839
                   [FStar_Syntax_Syntax.U_zero] in
               let uu____2840 =
                 let uu____2847 =
                   let uu____2853 = name ["FStar"; "Char"; "char"] in
                   (uu____2853, (Some (FStar_Syntax_Syntax.Implicit true))) in
                 [uu____2847] in
               (uu____2838, uu____2840) in
             FStar_Syntax_Syntax.Tm_app uu____2828 in
           mk uu____2827 in
         FStar_List.fold_right
           (fun c  ->
              fun a  ->
                let uu____2881 =
                  let uu____2882 =
                    let uu____2892 =
                      let uu____2893 = ctor ["Prims"; "Cons"] in
                      FStar_Syntax_Syntax.mk_Tm_uinst uu____2893
                        [FStar_Syntax_Syntax.U_zero] in
                    let uu____2894 =
                      let uu____2901 =
                        let uu____2907 = name ["FStar"; "Char"; "char"] in
                        (uu____2907,
                          (Some (FStar_Syntax_Syntax.Implicit true))) in
                      let uu____2913 =
                        let uu____2920 =
                          let uu____2926 =
                            mk
                              (FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_char c)) in
                          (uu____2926, None) in
                        [uu____2920; (a, None)] in
                      uu____2901 :: uu____2913 in
                    (uu____2892, uu____2894) in
                  FStar_Syntax_Syntax.Tm_app uu____2882 in
                mk uu____2881) uu____2822 uu____2824)) in
  [uu____2809]
let reduce_equality:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let is_decidable_equality t =
      let uu____2986 =
        let uu____2987 = FStar_Syntax_Util.un_uinst t in
        uu____2987.FStar_Syntax_Syntax.n in
      match uu____2986 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq
      | uu____2991 -> false in
    let is_propositional_equality t =
      let uu____2996 =
        let uu____2997 = FStar_Syntax_Util.un_uinst t in
        uu____2997.FStar_Syntax_Syntax.n in
      match uu____2996 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid
      | uu____3001 -> false in
    match tm.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app
        (op_eq_inst,(_typ,uu____3006)::(a1,uu____3008)::(a2,uu____3010)::[])
        when is_decidable_equality op_eq_inst ->
        let tt =
          let uu____3051 = FStar_Syntax_Util.eq_tm a1 a2 in
          match uu____3051 with
          | FStar_Syntax_Util.Equal  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool true)) tm.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Util.NotEqual  ->
              mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool false)) tm.FStar_Syntax_Syntax.pos
          | uu____3054 -> tm in
        tt
    | FStar_Syntax_Syntax.Tm_app (eq2_inst,_::(a1,_)::(a2,_)::[])
      |FStar_Syntax_Syntax.Tm_app (eq2_inst,(a1,_)::(a2,_)::[]) when
        is_propositional_equality eq2_inst ->
        let tt =
          let uu____3126 = FStar_Syntax_Util.eq_tm a1 a2 in
          match uu____3126 with
          | FStar_Syntax_Util.Equal  -> FStar_Syntax_Util.t_true
          | FStar_Syntax_Util.NotEqual  -> FStar_Syntax_Util.t_false
          | uu____3127 -> tm in
        tt
    | uu____3128 -> tm
let find_fv fv ops =
  match fv.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_List.tryFind
        (fun uu____3153  ->
           match uu____3153 with
           | (l,uu____3157) -> FStar_Syntax_Syntax.fv_eq_lid fv l) ops
  | uu____3158 -> None
let reduce_primops:
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let uu____3175 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops steps) in
      match uu____3175 with
      | true  -> tm
      | uu____3178 ->
          (match tm.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_app
               (fv,(a1,uu____3183)::(a2,uu____3185)::[]) ->
               let uu____3215 = find_fv fv arith_ops in
               (match uu____3215 with
                | None  -> tm
                | Some (uu____3235,op) ->
                    let norm i j =
                      let c =
                        let uu____3261 = FStar_Util.int_of_string i in
                        let uu____3262 = FStar_Util.int_of_string j in
                        op uu____3261 uu____3262 in
                      mk (FStar_Syntax_Syntax.Tm_constant c)
                        tm.FStar_Syntax_Syntax.pos in
                    let uu____3263 =
                      let uu____3266 =
                        let uu____3267 = FStar_Syntax_Subst.compress a1 in
                        uu____3267.FStar_Syntax_Syntax.n in
                      let uu____3270 =
                        let uu____3271 = FStar_Syntax_Subst.compress a2 in
                        uu____3271.FStar_Syntax_Syntax.n in
                      (uu____3266, uu____3270) in
                    (match uu____3263 with
                     | (FStar_Syntax_Syntax.Tm_app
                        (head1,(arg1,uu____3278)::[]),FStar_Syntax_Syntax.Tm_app
                        (head2,(arg2,uu____3281)::[])) ->
                         let uu____3324 =
                           let uu____3329 =
                             let uu____3330 =
                               FStar_Syntax_Subst.compress head1 in
                             uu____3330.FStar_Syntax_Syntax.n in
                           let uu____3333 =
                             let uu____3334 =
                               FStar_Syntax_Subst.compress head2 in
                             uu____3334.FStar_Syntax_Syntax.n in
                           let uu____3337 =
                             let uu____3338 =
                               FStar_Syntax_Subst.compress arg1 in
                             uu____3338.FStar_Syntax_Syntax.n in
                           let uu____3341 =
                             let uu____3342 =
                               FStar_Syntax_Subst.compress arg2 in
                             uu____3342.FStar_Syntax_Syntax.n in
                           (uu____3329, uu____3333, uu____3337, uu____3341) in
                         (match uu____3324 with
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
                              let uu____3369 =
                                mk (FStar_Syntax_Syntax.Tm_fvar fv1)
                                  tm.FStar_Syntax_Syntax.pos in
                              let uu____3372 =
                                let uu____3378 =
                                  let uu____3384 = norm i j in
                                  (uu____3384, None) in
                                [uu____3378] in
                              FStar_Syntax_Util.mk_app uu____3369 uu____3372
                          | uu____3400 -> tm)
                     | (FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_int
                        (i,None )),FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_int (j,None ))) -> norm i j
                     | uu____3417 -> tm))
           | FStar_Syntax_Syntax.Tm_app (fv,(a1,uu____3422)::[]) ->
               let uu____3444 = find_fv fv un_ops in
               (match uu____3444 with
                | None  -> tm
                | Some (uu____3464,op) ->
                    let uu____3480 =
                      let uu____3481 = FStar_Syntax_Subst.compress a1 in
                      uu____3481.FStar_Syntax_Syntax.n in
                    (match uu____3480 with
                     | FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_string (b,uu____3487)) ->
                         let uu____3490 =
                           FStar_Bytes.unicode_bytes_as_string b in
                         op uu____3490
                     | uu____3491 -> tm))
           | uu____3492 -> reduce_equality tm)
let maybe_simplify:
  step Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun steps  ->
    fun tm  ->
      let w t =
        let uu___150_3517 = t in
        {
          FStar_Syntax_Syntax.n = (uu___150_3517.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___150_3517.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___150_3517.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____3536 -> None in
      let simplify arg = ((simp_t (Prims.fst arg)), arg) in
      let uu____3563 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      match uu____3563 with
      | true  -> reduce_primops steps tm
      | uu____3566 ->
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
               let uu____3607 =
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
               (match uu____3607 with
                | true  ->
                    let uu____3610 =
                      FStar_All.pipe_right args (FStar_List.map simplify) in
                    (match uu____3610 with
                     | (Some (true ),_)::(_,(arg,_))::[]
                       |(_,(arg,_))::(Some (true ),_)::[] -> arg
                     | (Some (false ),_)::_::[]|_::(Some (false ),_)::[] ->
                         w FStar_Syntax_Util.t_false
                     | uu____3778 -> tm)
                | uu____3787 ->
                    let uu____3788 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Syntax_Const.or_lid in
                    (match uu____3788 with
                     | true  ->
                         let uu____3791 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify) in
                         (match uu____3791 with
                          | (Some (true ),_)::_::[]|_::(Some (true ),_)::[]
                              -> w FStar_Syntax_Util.t_true
                          | (Some (false ),_)::(_,(arg,_))::[]
                            |(_,(arg,_))::(Some (false ),_)::[] -> arg
                          | uu____3959 -> tm)
                     | uu____3968 ->
                         let uu____3969 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.imp_lid in
                         (match uu____3969 with
                          | true  ->
                              let uu____3972 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              (match uu____3972 with
                               | _::(Some (true ),_)::[]
                                 |(Some (false ),_)::_::[] ->
                                   w FStar_Syntax_Util.t_true
                               | (Some (true ),uu____4063)::(uu____4064,
                                                             (arg,uu____4066))::[]
                                   -> arg
                               | uu____4107 -> tm)
                          | uu____4116 ->
                              let uu____4117 =
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.not_lid in
                              (match uu____4117 with
                               | true  ->
                                   let uu____4120 =
                                     FStar_All.pipe_right args
                                       (FStar_List.map simplify) in
                                   (match uu____4120 with
                                    | (Some (true ),uu____4155)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (Some (false ),uu____4179)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____4203 -> tm)
                               | uu____4212 ->
                                   let uu____4213 =
                                     (FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Syntax_Const.forall_lid)
                                       ||
                                       (FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Syntax_Const.exists_lid) in
                                   (match uu____4213 with
                                    | true  ->
                                        (match args with
                                         | (t,_)::[]
                                           |(_,Some
                                             (FStar_Syntax_Syntax.Implicit
                                             _))::(t,_)::[] ->
                                             let uu____4258 =
                                               let uu____4259 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____4259.FStar_Syntax_Syntax.n in
                                             (match uu____4258 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (uu____4264::[],body,uu____4266)
                                                  ->
                                                  (match simp_t body with
                                                   | Some (true ) ->
                                                       w
                                                         FStar_Syntax_Util.t_true
                                                   | Some (false ) ->
                                                       w
                                                         FStar_Syntax_Util.t_false
                                                   | uu____4294 -> tm)
                                              | uu____4296 -> tm)
                                         | uu____4297 -> tm)
                                    | uu____4303 -> reduce_equality tm)))))
           | uu____4304 -> tm)
let is_norm_request hd args =
  let uu____4319 =
    let uu____4323 =
      let uu____4324 = FStar_Syntax_Util.un_uinst hd in
      uu____4324.FStar_Syntax_Syntax.n in
    (uu____4323, args) in
  match uu____4319 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4329::uu____4330::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4333::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____4335 -> false
let get_norm_request args =
  match args with
  | _::(tm,_)::[]|(tm,_)::[] -> tm
  | uu____4368 -> failwith "Impossible"
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____4464  ->
               let uu____4465 = FStar_Syntax_Print.tag_of_term t in
               let uu____4466 = FStar_Syntax_Print.term_to_string t in
               let uu____4467 = stack_to_string stack in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____4465
                 uu____4466 uu____4467);
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____4468 ->
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
               ((let uu____4515 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____4515) && (is_norm_request hd args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Syntax_Const.prims_lid))
               ->
               let tm = get_norm_request args in
               let s =
                 [Reify;
                 Beta;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 Zeta;
                 Iota;
                 Primops] in
               let cfg' =
                 let uu___151_4528 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___151_4528.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant]
                 } in
               let stack' = (Debug t) ::
                 (Steps ((cfg.steps), (cfg.delta_level))) :: stack in
               norm cfg' env stack' tm
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4532;
                  FStar_Syntax_Syntax.pos = uu____4533;
                  FStar_Syntax_Syntax.vars = uu____4534;_},a1::a2::rest)
               ->
               let uu____4568 = FStar_Syntax_Util.head_and_args t in
               (match uu____4568 with
                | (hd,uu____4579) ->
                    let t' =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (hd, [a1])) None
                        t.FStar_Syntax_Syntax.pos in
                    let t =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app (t', (a2 :: rest))) None
                        t.FStar_Syntax_Syntax.pos in
                    norm cfg env stack t)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____4634;
                  FStar_Syntax_Syntax.pos = uu____4635;
                  FStar_Syntax_Syntax.vars = uu____4636;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____4659 = FStar_Syntax_Util.head_and_args t in
               (match uu____4659 with
                | (reify_head,uu____4670) ->
                    let a =
                      let uu____4686 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (Prims.fst a) in
                      FStar_Syntax_Subst.compress uu____4686 in
                    (match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____4689);
                            FStar_Syntax_Syntax.tk = uu____4690;
                            FStar_Syntax_Syntax.pos = uu____4691;
                            FStar_Syntax_Syntax.vars = uu____4692;_},a::[])
                         -> norm cfg env stack (Prims.fst a)
                     | uu____4717 ->
                         let stack =
                           (App
                              (reify_head, None, (t.FStar_Syntax_Syntax.pos)))
                           :: stack in
                         norm cfg env stack a))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u = norm_universe cfg env u in
               let uu____4725 =
                 mk (FStar_Syntax_Syntax.Tm_type u) t.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____4725
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____4732 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               (match uu____4732 with
                | true  -> norm cfg env stack t'
                | uu____4733 ->
                    let us =
                      let uu____4735 =
                        let uu____4739 =
                          FStar_List.map (norm_universe cfg env) us in
                        (uu____4739, (t.FStar_Syntax_Syntax.pos)) in
                      UnivArgs uu____4735 in
                    let stack = us :: stack in norm cfg env stack t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___128_4748  ->
                         match uu___128_4748 with
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining 
                           |FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               (match Prims.op_Negation should_delta with
                | true  -> rebuild cfg env stack t
                | uu____4750 ->
                    let r_env =
                      let uu____4752 = FStar_Syntax_Syntax.range_of_fv f in
                      FStar_TypeChecker_Env.set_range cfg.tcenv uu____4752 in
                    let uu____4753 =
                      FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                        r_env
                        (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                    (match uu____4753 with
                     | None  ->
                         (log cfg
                            (fun uu____4764  ->
                               FStar_Util.print "Tm_fvar case 2\n" []);
                          rebuild cfg env stack t)
                     | Some (us,t) ->
                         (log cfg
                            (fun uu____4770  ->
                               let uu____4771 =
                                 FStar_Syntax_Print.term_to_string t0 in
                               let uu____4772 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2 ">>> Unfolded %s to %s\n"
                                 uu____4771 uu____4772);
                          (let n = FStar_List.length us in
                           match n > (Prims.parse_int "0") with
                           | true  ->
                               (match stack with
                                | (UnivArgs (us',uu____4779))::stack ->
                                    let env =
                                      FStar_All.pipe_right us'
                                        (FStar_List.fold_left
                                           (fun env  ->
                                              fun u  -> (Univ u) :: env) env) in
                                    norm cfg env stack t
                                | uu____4792 when
                                    FStar_All.pipe_right cfg.steps
                                      (FStar_List.contains EraseUniverses)
                                    -> norm cfg env stack t
                                | uu____4793 ->
                                    let uu____4794 =
                                      let uu____4795 =
                                        FStar_Syntax_Print.lid_to_string
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      FStar_Util.format1
                                        "Impossible: missing universe instantiation on %s"
                                        uu____4795 in
                                    failwith uu____4794)
                           | uu____4800 -> norm cfg env stack t))))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____4802 = lookup_bvar env x in
               (match uu____4802 with
                | Univ uu____4803 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env,t0,r,fix) ->
                    (match (Prims.op_Negation fix) ||
                             (Prims.op_Negation
                                (FStar_List.contains (Exclude Zeta) cfg.steps))
                     with
                     | true  ->
                         let uu____4818 = FStar_ST.read r in
                         (match uu____4818 with
                          | Some (env,t') ->
                              (log cfg
                                 (fun uu____4837  ->
                                    let uu____4838 =
                                      FStar_Syntax_Print.term_to_string t in
                                    let uu____4839 =
                                      FStar_Syntax_Print.term_to_string t' in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n"
                                      uu____4838 uu____4839);
                               (let uu____4840 =
                                  let uu____4841 =
                                    FStar_Syntax_Subst.compress t' in
                                  uu____4841.FStar_Syntax_Syntax.n in
                                match uu____4840 with
                                | FStar_Syntax_Syntax.Tm_abs uu____4844 ->
                                    norm cfg env stack t'
                                | uu____4859 -> rebuild cfg env stack t'))
                          | None  -> norm cfg env ((MemoLazy r) :: stack) t0)
                     | uu____4866 -> norm cfg env stack t0))
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____4892)::uu____4893 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____4898)::uu____4899 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____4905,uu____4906))::stack_rest ->
                    (match c with
                     | Univ uu____4909 -> norm cfg (c :: env) stack_rest t
                     | uu____4910 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____4913::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____4926  ->
                                         let uu____4927 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4927);
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
                                           (fun uu___129_4941  ->
                                              match uu___129_4941 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____4942 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____4944  ->
                                         let uu____4945 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4945);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____4956  ->
                                         let uu____4957 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____4957);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____4958 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____4965 ->
                                   let cfg =
                                     let uu___152_4973 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___152_4973.tcenv);
                                       delta_level =
                                         (uu___152_4973.delta_level)
                                     } in
                                   let uu____4974 = closure_as_term cfg env t in
                                   rebuild cfg env stack uu____4974)
                          | uu____4975::tl ->
                              (log cfg
                                 (fun uu____4985  ->
                                    let uu____4986 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____4986);
                               (let body =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body))))
                | (Steps (s,dl))::stack ->
                    norm
                      (let uu___153_5007 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___153_5007.tcenv);
                         delta_level = dl
                       }) env stack t
                | (MemoLazy r)::stack ->
                    (set_memo r (env, t);
                     log cfg
                       (fun uu____5020  ->
                          let uu____5021 =
                            FStar_Syntax_Print.term_to_string t in
                          FStar_Util.print1 "\tSet memo %s\n" uu____5021);
                     norm cfg env stack t)
                | (Debug _)::_
                  |(Meta _)::_|(Let _)::_|(App _)::_|(Abs _)::_|[] ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let uu____5032 = closure_as_term cfg env t in
                         rebuild cfg env stack uu____5032
                     | uu____5033 ->
                         let uu____5034 =
                           FStar_Syntax_Subst.open_term' bs body in
                         (match uu____5034 with
                          | (bs,body,opening) ->
                              let lopt =
                                match lopt with
                                | Some (FStar_Util.Inl l) ->
                                    let uu____5063 =
                                      let uu____5069 =
                                        let uu____5070 =
                                          let uu____5071 =
                                            l.FStar_Syntax_Syntax.comp () in
                                          FStar_Syntax_Subst.subst_comp
                                            opening uu____5071 in
                                        FStar_All.pipe_right uu____5070
                                          FStar_Syntax_Util.lcomp_of_comp in
                                      FStar_All.pipe_right uu____5069
                                        (fun _0_36  -> FStar_Util.Inl _0_36) in
                                    FStar_All.pipe_right uu____5063
                                      (fun _0_37  -> Some _0_37)
                                | uu____5096 -> lopt in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env  ->
                                        fun uu____5110  -> Dummy :: env) env) in
                              (log cfg
                                 (fun uu____5115  ->
                                    let uu____5116 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs) in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____5116);
                               norm cfg env'
                                 ((Abs
                                     (env, bs, env', lopt,
                                       (t.FStar_Syntax_Syntax.pos))) ::
                                 stack) body))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let stack =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____5150  ->
                         fun stack  ->
                           match uu____5150 with
                           | (a,aq) ->
                               let uu____5158 =
                                 let uu____5159 =
                                   let uu____5163 =
                                     let uu____5164 =
                                       let uu____5174 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____5174, false) in
                                     Clos uu____5164 in
                                   (uu____5163, aq,
                                     (t.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____5159 in
                               uu____5158 :: stack) args) in
               (log cfg
                  (fun uu____5196  ->
                     let uu____5197 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____5197);
                norm cfg env stack head)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               (match FStar_List.contains WHNF cfg.steps with
                | true  ->
                    (match (env, stack) with
                     | ([],[]) ->
                         let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                         let t =
                           mk
                             (FStar_Syntax_Syntax.Tm_refine
                                ((let uu___154_5218 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___154_5218.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___154_5218.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack t
                     | uu____5219 ->
                         let uu____5222 = closure_as_term cfg env t in
                         rebuild cfg env stack uu____5222)
                | uu____5223 ->
                    let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                    let uu____5225 =
                      FStar_Syntax_Subst.open_term [(x, None)] f in
                    (match uu____5225 with
                     | (closing,f) ->
                         let f = norm cfg (Dummy :: env) [] f in
                         let t =
                           let uu____5241 =
                             let uu____5242 =
                               let uu____5247 =
                                 FStar_Syntax_Subst.close closing f in
                               ((let uu___155_5248 = x in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___155_5248.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___155_5248.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t_x
                                 }), uu____5247) in
                             FStar_Syntax_Syntax.Tm_refine uu____5242 in
                           mk uu____5241 t.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack t))
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               (match FStar_List.contains WHNF cfg.steps with
                | true  ->
                    let uu____5261 = closure_as_term cfg env t in
                    rebuild cfg env stack uu____5261
                | uu____5262 ->
                    let uu____5263 = FStar_Syntax_Subst.open_comp bs c in
                    (match uu____5263 with
                     | (bs,c) ->
                         let c =
                           let uu____5269 =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun uu____5275  -> Dummy :: env) env) in
                           norm_comp cfg uu____5269 c in
                         let t =
                           let uu____5282 = norm_binders cfg env bs in
                           FStar_Syntax_Util.arrow uu____5282 c in
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
                | uu____5321 ->
                    let t1 = norm cfg env [] t1 in
                    (log cfg
                       (fun uu____5324  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc =
                        match tc with
                        | FStar_Util.Inl t ->
                            let uu____5337 = norm cfg env [] t in
                            FStar_Util.Inl uu____5337
                        | FStar_Util.Inr c ->
                            let uu____5345 = norm_comp cfg env c in
                            FStar_Util.Inr uu____5345 in
                      let uu____5346 =
                        mk (FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l))
                          t.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack uu____5346)))
           | FStar_Syntax_Syntax.Tm_match (head,branches) ->
               let stack =
                 (Match (env, branches, (t.FStar_Syntax_Syntax.pos))) ::
                 stack in
               norm cfg env stack head
           | FStar_Syntax_Syntax.Tm_let
               ((uu____5391,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____5392;
                              FStar_Syntax_Syntax.lbunivs = uu____5393;
                              FStar_Syntax_Syntax.lbtyp = uu____5394;
                              FStar_Syntax_Syntax.lbeff = uu____5395;
                              FStar_Syntax_Syntax.lbdef = uu____5396;_}::uu____5397),uu____5398)
               -> rebuild cfg env stack t
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____5424 =
                 (let uu____5425 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____5425) &&
                   ((FStar_Syntax_Util.is_pure_effect n) ||
                      ((FStar_Syntax_Util.is_ghost_effect n) &&
                         (let uu____5426 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____5426))) in
               (match uu____5424 with
                | true  ->
                    let env =
                      let uu____5429 =
                        let uu____5430 =
                          let uu____5440 = FStar_Util.mk_ref None in
                          (env, (lb.FStar_Syntax_Syntax.lbdef), uu____5440,
                            false) in
                        Clos uu____5430 in
                      uu____5429 :: env in
                    norm cfg env stack body
                | uu____5463 ->
                    let uu____5464 =
                      let uu____5467 =
                        let uu____5468 =
                          let uu____5469 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left in
                          FStar_All.pipe_right uu____5469
                            FStar_Syntax_Syntax.mk_binder in
                        [uu____5468] in
                      FStar_Syntax_Subst.open_term uu____5467 body in
                    (match uu____5464 with
                     | (bs,body) ->
                         let lb =
                           let uu___156_5475 = lb in
                           let uu____5476 =
                             let uu____5479 =
                               let uu____5480 = FStar_List.hd bs in
                               FStar_All.pipe_right uu____5480 Prims.fst in
                             FStar_All.pipe_right uu____5479
                               (fun _0_38  -> FStar_Util.Inl _0_38) in
                           let uu____5489 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let uu____5492 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = uu____5476;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___156_5475.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = uu____5489;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___156_5475.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5492
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env  -> fun uu____5502  -> Dummy :: env)
                                env) in
                         norm cfg env'
                           ((Let (env, bs, lb, (t.FStar_Syntax_Syntax.pos)))
                           :: stack) body))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____5518 = closure_as_term cfg env t in
               rebuild cfg env stack uu____5518
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____5531 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____5553  ->
                        match uu____5553 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____5592 =
                                let uu___157_5593 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_5593.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___157_5593.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____5592 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (Prims.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____5531 with
                | (rec_env,memos,uu____5653) ->
                    let uu____5668 =
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
                           fun env  ->
                             let uu____5710 =
                               let uu____5711 =
                                 let uu____5721 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____5721, false) in
                               Clos uu____5711 in
                             uu____5710 :: env) (Prims.snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____5759;
                             FStar_Syntax_Syntax.pos = uu____5760;
                             FStar_Syntax_Syntax.vars = uu____5761;_},uu____5762,uu____5763))::uu____5764
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____5770 -> false in
                    (match Prims.op_Negation should_reify with
                     | true  ->
                         let t = norm cfg env [] t in
                         let stack = (Steps ((cfg.steps), (cfg.delta_level)))
                           :: stack in
                         let cfg =
                           let uu___158_5776 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___158_5776.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta]
                           } in
                         norm cfg env
                           ((Meta
                               ((FStar_Syntax_Syntax.Meta_monadic (m, t)),
                                 (t.FStar_Syntax_Syntax.pos))) :: stack) head
                     | uu____5777 ->
                         let uu____5778 =
                           let uu____5779 = FStar_Syntax_Subst.compress head in
                           uu____5779.FStar_Syntax_Syntax.n in
                         (match uu____5778 with
                          | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body)
                              ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m in
                              let uu____5793 =
                                ed.FStar_Syntax_Syntax.bind_repr in
                              (match uu____5793 with
                               | (uu____5794,bind_repr) ->
                                   (match lb.FStar_Syntax_Syntax.lbname with
                                    | FStar_Util.Inl x ->
                                        let head =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify
                                            lb.FStar_Syntax_Syntax.lbdef in
                                        let body =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify body in
                                        let body =
                                          let uu____5816 =
                                            let uu____5819 =
                                              let uu____5820 =
                                                let uu____5835 =
                                                  let uu____5837 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x in
                                                  [uu____5837] in
                                                (uu____5835, body, None) in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____5820 in
                                            FStar_Syntax_Syntax.mk uu____5819 in
                                          uu____5816 None
                                            body.FStar_Syntax_Syntax.pos in
                                        let bind_inst =
                                          let uu____5863 =
                                            let uu____5864 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr in
                                            uu____5864.FStar_Syntax_Syntax.n in
                                          match uu____5863 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind,uu____5870::uu____5871::[])
                                              ->
                                              let uu____5877 =
                                                let uu____5880 =
                                                  let uu____5881 =
                                                    let uu____5886 =
                                                      let uu____5888 =
                                                        (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.tcenv
                                                          lb.FStar_Syntax_Syntax.lbtyp in
                                                      let uu____5889 =
                                                        let uu____5891 =
                                                          (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.tcenv t in
                                                        [uu____5891] in
                                                      uu____5888 ::
                                                        uu____5889 in
                                                    (bind, uu____5886) in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____5881 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____5880 in
                                              uu____5877 None
                                                t.FStar_Syntax_Syntax.pos
                                          | uu____5903 ->
                                              failwith
                                                "NIY : Reification of indexed effects" in
                                        let reified =
                                          let uu____5909 =
                                            let uu____5912 =
                                              let uu____5913 =
                                                let uu____5923 =
                                                  let uu____5925 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lb.FStar_Syntax_Syntax.lbtyp in
                                                  let uu____5926 =
                                                    let uu____5928 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t in
                                                    let uu____5929 =
                                                      let uu____5931 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun in
                                                      let uu____5932 =
                                                        let uu____5934 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head in
                                                        let uu____5935 =
                                                          let uu____5937 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu____5938 =
                                                            let uu____5940 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body in
                                                            [uu____5940] in
                                                          uu____5937 ::
                                                            uu____5938 in
                                                        uu____5934 ::
                                                          uu____5935 in
                                                      uu____5931 ::
                                                        uu____5932 in
                                                    uu____5928 :: uu____5929 in
                                                  uu____5925 :: uu____5926 in
                                                (bind_inst, uu____5923) in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____5913 in
                                            FStar_Syntax_Syntax.mk uu____5912 in
                                          uu____5909 None
                                            t.FStar_Syntax_Syntax.pos in
                                        let uu____5952 = FStar_List.tl stack in
                                        norm cfg env uu____5952 reified
                                    | FStar_Util.Inr uu____5953 ->
                                        failwith
                                          "Cannot reify a top-level let binding"))
                          | FStar_Syntax_Syntax.Tm_app (head,args) ->
                              let ed =
                                FStar_TypeChecker_Env.get_effect_decl
                                  cfg.tcenv m in
                              let uu____5971 =
                                ed.FStar_Syntax_Syntax.bind_repr in
                              (match uu____5971 with
                               | (uu____5972,bind_repr) ->
                                   let maybe_unfold_action head =
                                     let maybe_extract_fv t =
                                       let t =
                                         let uu____5995 =
                                           let uu____5996 =
                                             FStar_Syntax_Subst.compress t in
                                           uu____5996.FStar_Syntax_Syntax.n in
                                         match uu____5995 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (t,uu____6002) -> t
                                         | uu____6007 -> head in
                                       let uu____6008 =
                                         let uu____6009 =
                                           FStar_Syntax_Subst.compress t in
                                         uu____6009.FStar_Syntax_Syntax.n in
                                       match uu____6008 with
                                       | FStar_Syntax_Syntax.Tm_fvar x ->
                                           Some x
                                       | uu____6014 -> None in
                                     let uu____6015 = maybe_extract_fv head in
                                     match uu____6015 with
                                     | Some x when
                                         let uu____6021 =
                                           FStar_Syntax_Syntax.lid_of_fv x in
                                         FStar_TypeChecker_Env.is_action
                                           cfg.tcenv uu____6021
                                         ->
                                         let head = norm cfg env [] head in
                                         let action_unfolded =
                                           let uu____6025 =
                                             maybe_extract_fv head in
                                           match uu____6025 with
                                           | Some uu____6028 -> Some true
                                           | uu____6029 -> Some false in
                                         (head, action_unfolded)
                                     | uu____6032 -> (head, None) in
                                   let rec bind_on_lift args acc =
                                     match args with
                                     | [] ->
                                         (match FStar_List.rev acc with
                                          | [] ->
                                              failwith
                                                "bind_on_lift should be always called with a non-empty list"
                                          | (head,uu____6079)::args ->
                                              let uu____6094 =
                                                maybe_unfold_action head in
                                              (match uu____6094 with
                                               | (head,found_action) ->
                                                   let mk tm =
                                                     (FStar_Syntax_Syntax.mk
                                                        tm) None
                                                       t.FStar_Syntax_Syntax.pos in
                                                   let body =
                                                     mk
                                                       (FStar_Syntax_Syntax.Tm_app
                                                          (head, args)) in
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
                                         let uu____6140 =
                                           let uu____6141 =
                                             FStar_Syntax_Subst.compress e in
                                           uu____6141.FStar_Syntax_Syntax.n in
                                         (match uu____6140 with
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
                                                  "monadic_app_var" None t' in
                                              let body =
                                                let uu____6162 =
                                                  let uu____6168 =
                                                    let uu____6171 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x in
                                                    (uu____6171, q) in
                                                  uu____6168 :: acc in
                                                bind_on_lift es uu____6162 in
                                              let lifted_e0 =
                                                reify_lift cfg.tcenv e0 m1 m2
                                                  t' in
                                              let continuation =
                                                FStar_Syntax_Util.abs
                                                  [(x, None)] body
                                                  (Some
                                                     (FStar_Util.Inr (m2, []))) in
                                              let bind_inst =
                                                let uu____6195 =
                                                  let uu____6196 =
                                                    FStar_Syntax_Subst.compress
                                                      bind_repr in
                                                  uu____6196.FStar_Syntax_Syntax.n in
                                                match uu____6195 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (bind,uu____6202::uu____6203::[])
                                                    ->
                                                    let uu____6209 =
                                                      let uu____6212 =
                                                        let uu____6213 =
                                                          let uu____6218 =
                                                            let uu____6220 =
                                                              (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                cfg.tcenv t' in
                                                            let uu____6221 =
                                                              let uu____6223
                                                                =
                                                                (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                  cfg.tcenv t in
                                                              [uu____6223] in
                                                            uu____6220 ::
                                                              uu____6221 in
                                                          (bind, uu____6218) in
                                                        FStar_Syntax_Syntax.Tm_uinst
                                                          uu____6213 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____6212 in
                                                    uu____6209 None
                                                      e0.FStar_Syntax_Syntax.pos
                                                | uu____6235 ->
                                                    failwith
                                                      "NIY : Reification of indexed effects" in
                                              let uu____6238 =
                                                let uu____6241 =
                                                  let uu____6242 =
                                                    let uu____6252 =
                                                      let uu____6254 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t' in
                                                      let uu____6255 =
                                                        let uu____6257 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            t in
                                                        let uu____6258 =
                                                          let uu____6260 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu____6261 =
                                                            let uu____6263 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                lifted_e0 in
                                                            let uu____6264 =
                                                              let uu____6266
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  FStar_Syntax_Syntax.tun in
                                                              let uu____6267
                                                                =
                                                                let uu____6269
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    continuation in
                                                                [uu____6269] in
                                                              uu____6266 ::
                                                                uu____6267 in
                                                            uu____6263 ::
                                                              uu____6264 in
                                                          uu____6260 ::
                                                            uu____6261 in
                                                        uu____6257 ::
                                                          uu____6258 in
                                                      uu____6254 ::
                                                        uu____6255 in
                                                    (bind_inst, uu____6252) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6242 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6241 in
                                              uu____6238 None
                                                e0.FStar_Syntax_Syntax.pos
                                          | FStar_Syntax_Syntax.Tm_meta
                                              (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                               uu____6282)
                                              ->
                                              bind_on_lift es ((e0, q) ::
                                                acc)
                                          | uu____6298 ->
                                              bind_on_lift es ((e, q) :: acc)) in
                                   let binded_head =
                                     let uu____6304 =
                                       let uu____6308 =
                                         FStar_Syntax_Syntax.as_arg head in
                                       uu____6308 :: args in
                                     bind_on_lift uu____6304 [] in
                                   let uu____6313 = FStar_List.tl stack in
                                   norm cfg env uu____6313 binded_head)
                          | FStar_Syntax_Syntax.Tm_meta
                              (e,FStar_Syntax_Syntax.Meta_monadic_lift
                               (msrc,mtgt,t'))
                              ->
                              let lifted =
                                reify_lift cfg.tcenv e msrc mtgt t' in
                              norm cfg env stack lifted
                          | uu____6327 -> norm cfg env stack head))
                | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
                    let should_reify =
                      match stack with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____6336;
                             FStar_Syntax_Syntax.pos = uu____6337;
                             FStar_Syntax_Syntax.vars = uu____6338;_},uu____6339,uu____6340))::uu____6341
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____6347 -> false in
                    (match should_reify with
                     | true  ->
                         let uu____6348 = FStar_List.tl stack in
                         let uu____6349 = reify_lift cfg.tcenv head m m' t in
                         norm cfg env uu____6348 uu____6349
                     | uu____6350 ->
                         let uu____6351 =
                           ((FStar_Syntax_Util.is_pure_effect m) ||
                              (FStar_Syntax_Util.is_ghost_effect m))
                             &&
                             (FStar_All.pipe_right cfg.steps
                                (FStar_List.contains
                                   PureSubtermsWithinComputations)) in
                         (match uu____6351 with
                          | true  ->
                              let stack =
                                (Steps ((cfg.steps), (cfg.delta_level))) ::
                                stack in
                              let cfg =
                                let uu___159_6356 = cfg in
                                {
                                  steps =
                                    [PureSubtermsWithinComputations;
                                    Primops;
                                    AllowUnboundUniverses;
                                    EraseUniverses;
                                    Exclude Zeta];
                                  tcenv = (uu___159_6356.tcenv);
                                  delta_level =
                                    [FStar_TypeChecker_Env.Inlining;
                                    FStar_TypeChecker_Env.Eager_unfolding_only]
                                } in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m, m', t)),
                                      (head.FStar_Syntax_Syntax.pos))) ::
                                stack) head
                          | uu____6359 ->
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m, m', t)),
                                      (head.FStar_Syntax_Syntax.pos))) ::
                                stack) head))
                | uu____6362 ->
                    (match stack with
                     | uu____6363::uu____6364 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____6368)
                              -> norm cfg env ((Meta (m, r)) :: stack) head
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args),
                                      (t.FStar_Syntax_Syntax.pos))) :: stack)
                                head
                          | uu____6383 -> norm cfg env stack head)
                     | uu____6384 ->
                         let head = norm cfg env [] head in
                         let m =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____6394 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____6394
                           | uu____6401 -> m in
                         let t =
                           mk (FStar_Syntax_Syntax.Tm_meta (head, m))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild cfg env stack t)))
and reify_lift:
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
                let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
                let uu____6415 = ed.FStar_Syntax_Syntax.return_repr in
                (match uu____6415 with
                 | (uu____6416,return_repr) ->
                     let return_inst =
                       let uu____6423 =
                         let uu____6424 =
                           FStar_Syntax_Subst.compress return_repr in
                         uu____6424.FStar_Syntax_Syntax.n in
                       match uu____6423 with
                       | FStar_Syntax_Syntax.Tm_uinst
                           (return_tm,uu____6430::[]) ->
                           let uu____6436 =
                             let uu____6439 =
                               let uu____6440 =
                                 let uu____6445 =
                                   let uu____6447 =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env t in
                                   [uu____6447] in
                                 (return_tm, uu____6445) in
                               FStar_Syntax_Syntax.Tm_uinst uu____6440 in
                             FStar_Syntax_Syntax.mk uu____6439 in
                           uu____6436 None e.FStar_Syntax_Syntax.pos
                       | uu____6459 ->
                           failwith "NIY : Reification of indexed effects" in
                     let uu____6462 =
                       let uu____6465 =
                         let uu____6466 =
                           let uu____6476 =
                             let uu____6478 = FStar_Syntax_Syntax.as_arg t in
                             let uu____6479 =
                               let uu____6481 = FStar_Syntax_Syntax.as_arg e in
                               [uu____6481] in
                             uu____6478 :: uu____6479 in
                           (return_inst, uu____6476) in
                         FStar_Syntax_Syntax.Tm_app uu____6466 in
                       FStar_Syntax_Syntax.mk uu____6465 in
                     uu____6462 None e.FStar_Syntax_Syntax.pos)
            | uu____6493 ->
                failwith "NYI: non pure monadic lift normalisation"
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
                (fun uu____6523  ->
                   match uu____6523 with
                   | (a,imp) ->
                       let uu____6530 = norm cfg env [] a in
                       (uu____6530, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp = ghost_to_pure_aux cfg env comp in
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___160_6545 = comp in
            let uu____6548 =
              let uu____6549 =
                let uu____6555 = norm cfg env [] t in
                let uu____6556 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____6555, uu____6556) in
              FStar_Syntax_Syntax.Total uu____6549 in
            {
              FStar_Syntax_Syntax.n = uu____6548;
              FStar_Syntax_Syntax.tk = (uu___160_6545.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___160_6545.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___160_6545.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___161_6571 = comp in
            let uu____6574 =
              let uu____6575 =
                let uu____6581 = norm cfg env [] t in
                let uu____6582 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____6581, uu____6582) in
              FStar_Syntax_Syntax.GTotal uu____6575 in
            {
              FStar_Syntax_Syntax.n = uu____6574;
              FStar_Syntax_Syntax.tk = (uu___161_6571.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___161_6571.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___161_6571.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6613  ->
                      match uu____6613 with
                      | (a,i) ->
                          let uu____6620 = norm cfg env [] a in
                          (uu____6620, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___130_6625  ->
                      match uu___130_6625 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____6629 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____6629
                      | f -> f)) in
            let uu___162_6633 = comp in
            let uu____6636 =
              let uu____6637 =
                let uu___163_6638 = ct in
                let uu____6639 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____6640 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____6643 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____6639;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___163_6638.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____6640;
                  FStar_Syntax_Syntax.effect_args = uu____6643;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____6637 in
            {
              FStar_Syntax_Syntax.n = uu____6636;
              FStar_Syntax_Syntax.tk = (uu___162_6633.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___162_6633.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___162_6633.FStar_Syntax_Syntax.vars)
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
        let norm t =
          norm
            (let uu___164_6660 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___164_6660.tcenv);
               delta_level = (uu___164_6660.delta_level)
             }) env [] t in
        let non_info t =
          let uu____6665 = norm t in
          FStar_Syntax_Util.non_informative uu____6665 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____6668 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___165_6682 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___165_6682.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___165_6682.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___165_6682.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____6692 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            (match uu____6692 with
             | true  ->
                 let ct =
                   match downgrade_ghost_effect_name
                           ct.FStar_Syntax_Syntax.effect_name
                   with
                   | Some pure_eff ->
                       let uu___166_6697 = ct in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___166_6697.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name = pure_eff;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___166_6697.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___166_6697.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___166_6697.FStar_Syntax_Syntax.flags)
                       }
                   | None  ->
                       let ct = unfold_effect_abbrev cfg.tcenv c in
                       let uu___167_6699 = ct in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (uu___167_6699.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.result_typ =
                           (uu___167_6699.FStar_Syntax_Syntax.result_typ);
                         FStar_Syntax_Syntax.effect_args =
                           (uu___167_6699.FStar_Syntax_Syntax.effect_args);
                         FStar_Syntax_Syntax.flags =
                           (uu___167_6699.FStar_Syntax_Syntax.flags)
                       } in
                 let uu___168_6700 = c in
                 {
                   FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct);
                   FStar_Syntax_Syntax.tk =
                     (uu___168_6700.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___168_6700.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___168_6700.FStar_Syntax_Syntax.vars)
                 }
             | uu____6705 -> c)
        | uu____6706 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____6709  ->
        match uu____6709 with
        | (x,imp) ->
            let uu____6712 =
              let uu___169_6713 = x in
              let uu____6714 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___169_6713.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___169_6713.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____6714
              } in
            (uu____6712, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6720 =
          FStar_List.fold_left
            (fun uu____6727  ->
               fun b  ->
                 match uu____6727 with
                 | (nbs',env) ->
                     let b = norm_binder cfg env b in
                     ((b :: nbs'), (Dummy :: env))) ([], env) bs in
        match uu____6720 with | (nbs,uu____6744) -> FStar_List.rev nbs
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
            let uu____6761 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            (match uu____6761 with
             | true  ->
                 let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
                 let uu____6766 = FStar_Syntax_Util.is_total_lcomp lc in
                 (match uu____6766 with
                  | true  ->
                      let uu____6770 =
                        let uu____6773 =
                          let uu____6774 =
                            let uu____6777 = FStar_Syntax_Syntax.mk_Total t in
                            FStar_Syntax_Util.comp_set_flags uu____6777 flags in
                          FStar_Syntax_Util.lcomp_of_comp uu____6774 in
                        FStar_Util.Inl uu____6773 in
                      Some uu____6770
                  | uu____6780 ->
                      let uu____6781 =
                        let uu____6784 =
                          let uu____6785 =
                            let uu____6788 = FStar_Syntax_Syntax.mk_GTotal t in
                            FStar_Syntax_Util.comp_set_flags uu____6788 flags in
                          FStar_Syntax_Util.lcomp_of_comp uu____6785 in
                        FStar_Util.Inl uu____6784 in
                      Some uu____6781)
             | uu____6791 ->
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____6801 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          match stack with
          | [] -> t
          | (Debug tm)::stack ->
              ((let uu____6813 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                match uu____6813 with
                | true  ->
                    let uu____6814 = FStar_Syntax_Print.term_to_string tm in
                    let uu____6815 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print2 "Normalized %s to %s\n" uu____6814
                      uu____6815
                | uu____6816 -> ());
               rebuild cfg env stack t)
          | (Steps (s,dl))::stack ->
              rebuild
                (let uu___170_6823 = cfg in
                 { steps = s; tcenv = (uu___170_6823.tcenv); delta_level = dl
                 }) env stack t
          | (Meta (m,r))::stack ->
              let t = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack t
          | (MemoLazy r)::stack ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____6843  ->
                    let uu____6844 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____6844);
               rebuild cfg env stack t)
          | (Let (env',bs,lb,r))::stack ->
              let body = FStar_Syntax_Subst.close bs t in
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) None r in
              rebuild cfg env' stack t
          | (Abs (env',bs,env'',lopt,r))::stack ->
              let bs = norm_binders cfg env' bs in
              let lopt = norm_lcomp_opt cfg env'' lopt in
              let uu____6881 =
                let uu___171_6882 = FStar_Syntax_Util.abs bs t lopt in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___171_6882.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___171_6882.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___171_6882.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack uu____6881
          | (Arg (Univ _,_,_))::_|(Arg (Dummy ,_,_))::_ ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack ->
              let t = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack t
          | (Arg (Clos (env,tm,m,uu____6904),aq,r))::stack ->
              (log cfg
                 (fun uu____6920  ->
                    let uu____6921 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____6921);
               (match FStar_List.contains (Exclude Iota) cfg.steps with
                | true  ->
                    (match FStar_List.contains WHNF cfg.steps with
                     | true  ->
                         let arg = closure_as_term cfg env tm in
                         let t =
                           FStar_Syntax_Syntax.extend_app t (arg, aq) None r in
                         rebuild cfg env stack t
                     | uu____6928 ->
                         let stack = (App (t, aq, r)) :: stack in
                         norm cfg env stack tm)
                | uu____6931 ->
                    let uu____6932 = FStar_ST.read m in
                    (match uu____6932 with
                     | None  ->
                         (match FStar_List.contains WHNF cfg.steps with
                          | true  ->
                              let arg = closure_as_term cfg env tm in
                              let t =
                                FStar_Syntax_Syntax.extend_app t (arg, aq)
                                  None r in
                              rebuild cfg env stack t
                          | uu____6952 ->
                              let stack = (MemoLazy m) :: (App (t, aq, r)) ::
                                stack in
                              norm cfg env stack tm)
                     | Some (uu____6958,a) ->
                         let t =
                           FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                         rebuild cfg env stack t)))
          | (App (head,aq,r))::stack ->
              let t = FStar_Syntax_Syntax.extend_app head (t, aq) None r in
              let uu____6980 = maybe_simplify cfg.steps t in
              rebuild cfg env stack uu____6980
          | (Match (env,branches,r))::stack ->
              (log cfg
                 (fun uu____6987  ->
                    let uu____6988 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____6988);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____6993 =
                  let whnf = FStar_List.contains WHNF cfg.steps in
                  let cfg_exclude_iota_zeta =
                    let new_delta =
                      FStar_All.pipe_right cfg.delta_level
                        (FStar_List.filter
                           (fun uu___131_7000  ->
                              match uu___131_7000 with
                              | FStar_TypeChecker_Env.Inlining 
                                |FStar_TypeChecker_Env.Eager_unfolding_only 
                                  -> true
                              | uu____7001 -> false)) in
                    let steps' =
                      let uu____7004 =
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains PureSubtermsWithinComputations) in
                      match uu____7004 with
                      | true  -> [Exclude Zeta]
                      | uu____7006 -> [Exclude Iota; Exclude Zeta] in
                    let uu___172_7007 = cfg in
                    {
                      steps = (FStar_List.append steps' cfg.steps);
                      tcenv = (uu___172_7007.tcenv);
                      delta_level = new_delta
                    } in
                  let norm_or_whnf env t =
                    match whnf with
                    | true  -> closure_as_term cfg_exclude_iota_zeta env t
                    | uu____7017 -> norm cfg_exclude_iota_zeta env [] t in
                  let rec norm_pat env p =
                    match p.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_constant uu____7041 -> (p, env)
                    | FStar_Syntax_Syntax.Pat_disj [] ->
                        failwith "Impossible"
                    | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                        let uu____7061 = norm_pat env hd in
                        (match uu____7061 with
                         | (hd,env') ->
                             let tl =
                               FStar_All.pipe_right tl
                                 (FStar_List.map
                                    (fun p  ->
                                       let uu____7097 = norm_pat env p in
                                       Prims.fst uu____7097)) in
                             ((let uu___173_7109 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_disj (hd :: tl));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___173_7109.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___173_7109.FStar_Syntax_Syntax.p)
                               }), env'))
                    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                        let uu____7126 =
                          FStar_All.pipe_right pats
                            (FStar_List.fold_left
                               (fun uu____7160  ->
                                  fun uu____7161  ->
                                    match (uu____7160, uu____7161) with
                                    | ((pats,env),(p,b)) ->
                                        let uu____7226 = norm_pat env p in
                                        (match uu____7226 with
                                         | (p,env) -> (((p, b) :: pats), env)))
                               ([], env)) in
                        (match uu____7126 with
                         | (pats,env) ->
                             ((let uu___174_7292 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_cons
                                      (fv, (FStar_List.rev pats)));
                                 FStar_Syntax_Syntax.ty =
                                   (uu___174_7292.FStar_Syntax_Syntax.ty);
                                 FStar_Syntax_Syntax.p =
                                   (uu___174_7292.FStar_Syntax_Syntax.p)
                               }), env))
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let x =
                          let uu___175_7306 = x in
                          let uu____7307 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___175_7306.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___175_7306.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7307
                          } in
                        ((let uu___176_7313 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var x);
                            FStar_Syntax_Syntax.ty =
                              (uu___176_7313.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___176_7313.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let x =
                          let uu___177_7318 = x in
                          let uu____7319 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___177_7318.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___177_7318.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7319
                          } in
                        ((let uu___178_7325 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild x);
                            FStar_Syntax_Syntax.ty =
                              (uu___178_7325.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___178_7325.FStar_Syntax_Syntax.p)
                          }), (Dummy :: env))
                    | FStar_Syntax_Syntax.Pat_dot_term (x,t) ->
                        let x =
                          let uu___179_7335 = x in
                          let uu____7336 =
                            norm_or_whnf env x.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___179_7335.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___179_7335.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____7336
                          } in
                        let t = norm_or_whnf env t in
                        ((let uu___180_7343 = p in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x, t));
                            FStar_Syntax_Syntax.ty =
                              (uu___180_7343.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___180_7343.FStar_Syntax_Syntax.p)
                          }), env) in
                  let branches =
                    match env with
                    | [] when whnf -> branches
                    | uu____7347 ->
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun branch  ->
                                let uu____7350 =
                                  FStar_Syntax_Subst.open_branch branch in
                                match uu____7350 with
                                | (p,wopt,e) ->
                                    let uu____7368 = norm_pat env p in
                                    (match uu____7368 with
                                     | (p,env) ->
                                         let wopt =
                                           match wopt with
                                           | None  -> None
                                           | Some w ->
                                               let uu____7392 =
                                                 norm_or_whnf env w in
                                               Some uu____7392 in
                                         let e = norm_or_whnf env e in
                                         FStar_Syntax_Util.branch
                                           (p, wopt, e)))) in
                  let uu____7397 =
                    mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches)) r in
                  rebuild cfg env stack uu____7397 in
                let rec is_cons head =
                  match head.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____7407) -> is_cons h
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
                  | uu____7418 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | None  -> b
                  | Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee p =
                  let scrutinee = FStar_Syntax_Util.unmeta scrutinee in
                  let uu____7517 = FStar_Syntax_Util.head_and_args scrutinee in
                  match uu____7517 with
                  | (head,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_disj ps ->
                           let mopt =
                             FStar_Util.find_map ps
                               (fun p  ->
                                  let m = matches_pat scrutinee p in
                                  match m with
                                  | FStar_Util.Inl uu____7574 -> Some m
                                  | FStar_Util.Inr (true ) -> Some m
                                  | FStar_Util.Inr (false ) -> None) in
                           (match mopt with
                            | None  -> FStar_Util.Inr false
                            | Some m -> m)
                       | FStar_Syntax_Syntax.Pat_var _
                         |FStar_Syntax_Syntax.Pat_wild _ ->
                           FStar_Util.Inl [scrutinee]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____7605 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____7617 ->
                                let uu____7618 =
                                  let uu____7619 = is_cons head in
                                  Prims.op_Negation uu____7619 in
                                FStar_Util.Inr uu____7618)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____7633 =
                             let uu____7634 = FStar_Syntax_Util.un_uinst head in
                             uu____7634.FStar_Syntax_Syntax.n in
                           (match uu____7633 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____7641 ->
                                let uu____7642 =
                                  let uu____7643 = is_cons head in
                                  Prims.op_Negation uu____7643 in
                                FStar_Util.Inr uu____7642))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____7677)::rest_a,(p,uu____7680)::rest_p) ->
                      let uu____7708 = matches_pat t p in
                      (match uu____7708 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____7722 -> FStar_Util.Inr false in
                let rec matches scrutinee p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p,wopt,b)::rest ->
                      let uu____7793 = matches_pat scrutinee p in
                      (match uu____7793 with
                       | FStar_Util.Inr (false ) -> matches scrutinee rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____7803  ->
                                 let uu____7804 =
                                   FStar_Syntax_Print.pat_to_string p in
                                 let uu____7805 =
                                   let uu____7806 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____7806
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____7804 uu____7805);
                            (let env =
                               FStar_List.fold_left
                                 (fun env  ->
                                    fun t  ->
                                      let uu____7815 =
                                        let uu____7816 =
                                          let uu____7826 =
                                            FStar_Util.mk_ref (Some ([], t)) in
                                          ([], t, uu____7826, false) in
                                        Clos uu____7816 in
                                      uu____7815 :: env) env s in
                             let uu____7849 = guard_when_clause wopt b rest in
                             norm cfg env stack uu____7849))) in
                let uu____7850 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                match uu____7850 with
                | true  -> norm_and_rebuild_match ()
                | uu____7851 -> matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___132_7864  ->
                match uu___132_7864 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | uu____7867 -> [])) in
      let d =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____7871 -> d in
      { steps = s; tcenv = e; delta_level = d }
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____7882 = config s e in norm uu____7882 [] [] t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____7892 = config s e in norm_comp uu____7892 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  -> let uu____7899 = config [] env in norm_universe uu____7899 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____7906 = config [] env in ghost_to_pure_aux uu____7906 [] c
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
        let uu____7918 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____7918 in
      let uu____7919 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      match uu____7919 with
      | true  ->
          (match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
           with
           | Some pure_eff ->
               let uu___181_7921 = lc in
               {
                 FStar_Syntax_Syntax.eff_name = pure_eff;
                 FStar_Syntax_Syntax.res_typ =
                   (uu___181_7921.FStar_Syntax_Syntax.res_typ);
                 FStar_Syntax_Syntax.cflags =
                   (uu___181_7921.FStar_Syntax_Syntax.cflags);
                 FStar_Syntax_Syntax.comp =
                   ((fun uu____7922  ->
                       let uu____7923 = lc.FStar_Syntax_Syntax.comp () in
                       ghost_to_pure env uu____7923))
               }
           | None  -> lc)
      | uu____7924 -> lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____7931 = normalize [AllowUnboundUniverses] env t in
      FStar_Syntax_Print.term_to_string uu____7931
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____7938 =
        let uu____7939 = config [AllowUnboundUniverses] env in
        norm_comp uu____7939 [] c in
      FStar_Syntax_Print.comp_to_string uu____7938
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
        let rec aux t =
          let t = FStar_Syntax_Subst.compress t in
          match t.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t0 = aux x.FStar_Syntax_Syntax.sort in
              (match t0.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____7976 =
                     let uu____7977 =
                       let uu____7982 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____7982) in
                     FStar_Syntax_Syntax.Tm_refine uu____7977 in
                   mk uu____7976 t0.FStar_Syntax_Syntax.pos
               | uu____7987 -> t)
          | uu____7988 -> t in
        aux t
let eta_expand_with_type:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun sort  ->
      let uu____7995 = FStar_Syntax_Util.arrow_formals_comp sort in
      match uu____7995 with
      | (binders,c) ->
          (match binders with
           | [] -> t
           | uu____8011 ->
               let uu____8015 =
                 FStar_All.pipe_right binders
                   FStar_Syntax_Util.args_of_binders in
               (match uu____8015 with
                | (binders,args) ->
                    let uu____8025 =
                      (FStar_Syntax_Syntax.mk_Tm_app t args) None
                        t.FStar_Syntax_Syntax.pos in
                    let uu____8030 =
                      let uu____8037 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.lcomp_of_comp c)
                          (fun _0_39  -> FStar_Util.Inl _0_39) in
                      FStar_All.pipe_right uu____8037
                        (fun _0_40  -> Some _0_40) in
                    FStar_Syntax_Util.abs binders uu____8025 uu____8030))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____8073 =
        let uu____8077 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____8077, (t.FStar_Syntax_Syntax.n)) in
      match uu____8073 with
      | (Some sort,uu____8084) ->
          let uu____8086 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type t uu____8086
      | (uu____8087,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type t x.FStar_Syntax_Syntax.sort
      | uu____8091 ->
          let uu____8095 = FStar_Syntax_Util.head_and_args t in
          (match uu____8095 with
           | (head,args) ->
               let uu____8121 =
                 let uu____8122 = FStar_Syntax_Subst.compress head in
                 uu____8122.FStar_Syntax_Syntax.n in
               (match uu____8121 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____8125,thead) ->
                    let uu____8139 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____8139 with
                     | (formals,tres) ->
                         (match (FStar_List.length formals) =
                                  (FStar_List.length args)
                          with
                          | true  -> t
                          | uu____8169 ->
                              let uu____8170 =
                                env.FStar_TypeChecker_Env.type_of
                                  (let uu___182_8174 = env in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___182_8174.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___182_8174.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___182_8174.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___182_8174.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___182_8174.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___182_8174.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       None;
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___182_8174.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___182_8174.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___182_8174.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___182_8174.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___182_8174.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___182_8174.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___182_8174.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___182_8174.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___182_8174.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___182_8174.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___182_8174.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___182_8174.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___182_8174.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___182_8174.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       true;
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___182_8174.FStar_TypeChecker_Env.qname_and_index)
                                   }) t in
                              (match uu____8170 with
                               | (uu____8175,ty,uu____8177) ->
                                   eta_expand_with_type t ty)))
                | uu____8178 ->
                    let uu____8179 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___183_8183 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___183_8183.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___183_8183.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___183_8183.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___183_8183.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___183_8183.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___183_8183.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___183_8183.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___183_8183.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___183_8183.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___183_8183.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___183_8183.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___183_8183.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___183_8183.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___183_8183.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___183_8183.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___183_8183.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___183_8183.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___183_8183.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___183_8183.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___183_8183.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___183_8183.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____8179 with
                     | (uu____8184,ty,uu____8186) ->
                         eta_expand_with_type t ty)))