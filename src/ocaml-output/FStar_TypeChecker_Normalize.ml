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
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____68 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____72 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____76 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____80 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____84 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____88 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____92 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____96 -> false
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
    match projectee with | Clos _0 -> true | uu____211 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____250 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____261 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
  fun uu___135_265  ->
    match uu___135_265 with
    | Clos (uu____266,t,uu____268,uu____269) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____280 -> "Univ"
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
    match projectee with | Arg _0 -> true | uu____427 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____451 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____475 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____502 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____531 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____570 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____593 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____615 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____644 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____671 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____683 =
      let uu____684 = FStar_Syntax_Util.un_uinst t in
      uu____684.FStar_Syntax_Syntax.n in
    match uu____683 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_refl_embed_lid
    | uu____688 -> false
let is_fstar_tactics_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____692 =
      let uu____693 = FStar_Syntax_Util.un_uinst t in
      uu____693.FStar_Syntax_Syntax.n in
    match uu____692 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.by_tactic_lid
    | uu____697 -> false
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____737 = FStar_ST.read r in
  match uu____737 with
  | Some uu____742 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____751 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____751 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___136_756  ->
    match uu___136_756 with
    | Arg (c,uu____758,uu____759) ->
        let uu____760 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____760
    | MemoLazy uu____761 -> "MemoLazy"
    | Abs (uu____765,bs,uu____767,uu____768,uu____769) ->
        let uu____776 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____776
    | UnivArgs uu____783 -> "UnivArgs"
    | Match uu____787 -> "Match"
    | App (t,uu____792,uu____793) ->
        let uu____794 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____794
    | Meta (m,uu____796) -> "Meta"
    | Let uu____797 -> "Let"
    | Steps (uu____802,uu____803,uu____804) -> "Steps"
    | Debug t ->
        let uu____810 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____810
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____816 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____816 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____830 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____830 then f () else ()
let is_empty uu___137_839 =
  match uu___137_839 with | [] -> true | uu____841 -> false
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____859 ->
      let uu____860 =
        let uu____861 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____861 in
      failwith uu____860
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
          let uu____892 =
            FStar_List.fold_left
              (fun uu____901  ->
                 fun u1  ->
                   match uu____901 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____916 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____916 with
                        | (k_u,n1) ->
                            let uu____925 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____925
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____892 with
          | (uu____935,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____951 = FStar_List.nth env x in
                 match uu____951 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____954 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____958 ->
                   let uu____959 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____959
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____963 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____966 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____971 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____971 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____982 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____982 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____987 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____990 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____990 with
                                  | (uu____993,m) -> n1 <= m)) in
                        if uu____987 then rest1 else us1
                    | uu____997 -> us1)
               | uu____1000 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1003 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1003 in
        let uu____1005 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1005
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1007 = aux u in
           match uu____1007 with
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
          (fun uu____1104  ->
             let uu____1105 = FStar_Syntax_Print.tag_of_term t in
             let uu____1106 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1105
               uu____1106);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1107 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1110 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1131 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1132 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1133 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1134 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1144 =
                    let uu____1145 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1145 in
                  mk uu____1144 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1152 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1152
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1154 = lookup_bvar env x in
                  (match uu____1154 with
                   | Univ uu____1155 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1159) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____1227 = closures_as_binders_delayed cfg env bs in
                  (match uu____1227 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1247 =
                         let uu____1248 =
                           let uu____1263 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1263) in
                         FStar_Syntax_Syntax.Tm_abs uu____1248 in
                       mk uu____1247 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1293 = closures_as_binders_delayed cfg env bs in
                  (match uu____1293 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____1324 =
                    let uu____1331 =
                      let uu____1335 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1335] in
                    closures_as_binders_delayed cfg env uu____1331 in
                  (match uu____1324 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1349 =
                         let uu____1350 =
                           let uu____1355 =
                             let uu____1356 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1356
                               FStar_Pervasives.fst in
                           (uu____1355, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1350 in
                       mk uu____1349 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____1424 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1424
                    | FStar_Util.Inr c ->
                        let uu____1438 = close_comp cfg env c in
                        FStar_Util.Inr uu____1438 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1453 =
                    let uu____1454 =
                      let uu____1472 = closure_as_term_delayed cfg env t11 in
                      (uu____1472, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1454 in
                  mk uu____1453 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1510 =
                    let uu____1511 =
                      let uu____1516 = closure_as_term_delayed cfg env t' in
                      let uu____1519 =
                        let uu____1520 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1520 in
                      (uu____1516, uu____1519) in
                    FStar_Syntax_Syntax.Tm_meta uu____1511 in
                  mk uu____1510 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1562 =
                    let uu____1563 =
                      let uu____1568 = closure_as_term_delayed cfg env t' in
                      let uu____1571 =
                        let uu____1572 =
                          let uu____1577 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1577) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1572 in
                      (uu____1568, uu____1571) in
                    FStar_Syntax_Syntax.Tm_meta uu____1563 in
                  mk uu____1562 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1596 =
                    let uu____1597 =
                      let uu____1602 = closure_as_term_delayed cfg env t' in
                      let uu____1605 =
                        let uu____1606 =
                          let uu____1612 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1612) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1606 in
                      (uu____1602, uu____1605) in
                    FStar_Syntax_Syntax.Tm_meta uu____1597 in
                  mk uu____1596 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1625 =
                    let uu____1626 =
                      let uu____1631 = closure_as_term_delayed cfg env t' in
                      (uu____1631, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1626 in
                  mk uu____1625 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____1652  -> Dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
                    | FStar_Util.Inr uu____1663 -> body
                    | FStar_Util.Inl uu____1664 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___150_1666 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___150_1666.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___150_1666.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___150_1666.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((uu____1673,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1697  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1702 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1702
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1706  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___151_1709 = lb in
                    let uu____1710 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1713 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___151_1709.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___151_1709.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1710;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___151_1709.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1713
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____1724  -> fun env1  -> Dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____1779 =
                    match uu____1779 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1825 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1841 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1875  ->
                                        fun uu____1876  ->
                                          match (uu____1875, uu____1876) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1941 =
                                                norm_pat env3 p1 in
                                              (match uu____1941 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1841 with
                               | (pats1,env3) ->
                                   ((let uu___152_2007 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
                                         (uu___152_2007.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___152_2007.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___153_2021 = x in
                                let uu____2022 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___153_2021.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___153_2021.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2022
                                } in
                              ((let uu___154_2028 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___154_2028.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___154_2028.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___155_2033 = x in
                                let uu____2034 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___155_2033.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___155_2033.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2034
                                } in
                              ((let uu___156_2040 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
                                    (uu___156_2040.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___156_2040.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___157_2050 = x in
                                let uu____2051 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___157_2050.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___157_2050.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____2051
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___158_2058 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___158_2058.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___158_2058.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____2061 = norm_pat env1 pat in
                        (match uu____2061 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
                                   let uu____2085 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2085 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2090 =
                    let uu____2091 =
                      let uu____2107 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2107) in
                    FStar_Syntax_Syntax.Tm_match uu____2091 in
                  mk uu____2090 t1.FStar_Syntax_Syntax.pos))
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
        | uu____2160 -> closure_as_term cfg env t
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
        | uu____2176 ->
            FStar_List.map
              (fun uu____2186  ->
                 match uu____2186 with
                 | (x,imp) ->
                     let uu____2201 = closure_as_term_delayed cfg env x in
                     (uu____2201, imp)) args
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
        let uu____2213 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2237  ->
                  fun uu____2238  ->
                    match (uu____2237, uu____2238) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___159_2282 = b in
                          let uu____2283 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___159_2282.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___159_2282.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2283
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2213 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____2330 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2342 = closure_as_term_delayed cfg env t in
                 let uu____2343 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2342 uu____2343
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2353 = closure_as_term_delayed cfg env t in
                 let uu____2354 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2353 uu____2354
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
                        (fun uu___138_2370  ->
                           match uu___138_2370 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2374 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2374
                           | f -> f)) in
                 let uu____2378 =
                   let uu___160_2379 = c1 in
                   let uu____2380 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2380;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___160_2379.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____2378)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
         (fun uu___139_2384  ->
            match uu___139_2384 with
            | FStar_Syntax_Syntax.DECREASES uu____2385 -> false
            | uu____2388 -> true))
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
            let uu____2416 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2416
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
              (let uu____2433 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2433
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
        | uu____2459 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2483 =
      let uu____2484 =
        let uu____2490 = FStar_Util.string_of_int i in (uu____2490, None) in
      FStar_Const.Const_int uu____2484 in
    const_as_tm uu____2483 p in
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
  let arg_as_int uu____2517 =
    match uu____2517 with
    | (a,uu____2522) ->
        let uu____2524 =
          let uu____2525 = FStar_Syntax_Subst.compress a in
          uu____2525.FStar_Syntax_Syntax.n in
        (match uu____2524 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2535 = FStar_Util.int_of_string i in Some uu____2535
         | uu____2536 -> None) in
  let arg_as_bounded_int uu____2545 =
    match uu____2545 with
    | (a,uu____2552) ->
        let uu____2556 =
          let uu____2557 = FStar_Syntax_Subst.compress a in
          uu____2557.FStar_Syntax_Syntax.n in
        (match uu____2556 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2564;
                FStar_Syntax_Syntax.pos = uu____2565;
                FStar_Syntax_Syntax.vars = uu____2566;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
                                                              = uu____2568;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2569;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2570;_},uu____2571)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____2602 =
               let uu____2605 = FStar_Util.int_of_string i in
               (fv1, uu____2605) in
             Some uu____2602
         | uu____2608 -> None) in
  let arg_as_bool uu____2617 =
    match uu____2617 with
    | (a,uu____2622) ->
        let uu____2624 =
          let uu____2625 = FStar_Syntax_Subst.compress a in
          uu____2625.FStar_Syntax_Syntax.n in
        (match uu____2624 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2630 -> None) in
  let arg_as_char uu____2637 =
    match uu____2637 with
    | (a,uu____2642) ->
        let uu____2644 =
          let uu____2645 = FStar_Syntax_Subst.compress a in
          uu____2645.FStar_Syntax_Syntax.n in
        (match uu____2644 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2650 -> None) in
  let arg_as_string uu____2657 =
    match uu____2657 with
    | (a,uu____2662) ->
        let uu____2664 =
          let uu____2665 = FStar_Syntax_Subst.compress a in
          uu____2665.FStar_Syntax_Syntax.n in
        (match uu____2664 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2670)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2673 -> None) in
  let arg_as_list f uu____2694 =
    match uu____2694 with
    | (a,uu____2703) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2722 -> None
          | (Some x)::xs ->
              let uu____2732 = sequence xs in
              (match uu____2732 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2743 = FStar_Syntax_Util.list_elements a in
        (match uu____2743 with
         | None  -> None
         | Some elts ->
             let uu____2753 =
               FStar_List.map
                 (fun x  ->
                    let uu____2758 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2758) elts in
             sequence uu____2753) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2788 = f a in Some uu____2788
    | uu____2789 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2828 = f a0 a1 in Some uu____2828
    | uu____2829 -> None in
  let unary_op as_a f r args =
    let uu____2873 = FStar_List.map as_a args in lift_unary (f r) uu____2873 in
  let binary_op as_a f r args =
    let uu____2923 = FStar_List.map as_a args in lift_binary (f r) uu____2923 in
  let as_primitive_step uu____2940 =
    match uu____2940 with
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
      (fun r  -> fun x  -> let uu____2978 = f x in int_as_const r uu____2978) in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3001 = f x y in int_as_const r uu____3001) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____3018 = f x in bool_as_const r uu____3018) in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3041 = f x y in bool_as_const r uu____3041) in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  -> let uu____3064 = f x y in string_as_const r uu____3064) in
  let list_of_string' rng s =
    let name l =
      let uu____3078 =
        let uu____3079 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3079 in
      mk uu____3078 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3089 =
      let uu____3091 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3091 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3089 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in int_as_const rng r in
  let string_concat' rng args =
    match args with
    | a1::a2::[] ->
        let uu____3145 = arg_as_string a1 in
        (match uu____3145 with
         | Some s1 ->
             let uu____3149 = arg_as_list arg_as_string a2 in
             (match uu____3149 with
              | Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____3157 = string_as_const rng r in Some uu____3157
              | uu____3158 -> None)
         | uu____3161 -> None)
    | uu____3163 -> None in
  let string_of_int1 rng i =
    let uu____3174 = FStar_Util.string_of_int i in
    string_as_const rng uu____3174 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3190 = FStar_Util.string_of_int i in
    string_as_const rng uu____3190 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3209 =
      let uu____3219 =
        let uu____3229 =
          let uu____3239 =
            let uu____3249 =
              let uu____3259 =
                let uu____3269 =
                  let uu____3279 =
                    let uu____3289 =
                      let uu____3299 =
                        let uu____3309 =
                          let uu____3319 =
                            let uu____3329 =
                              let uu____3339 =
                                let uu____3349 =
                                  let uu____3359 =
                                    let uu____3369 =
                                      let uu____3379 =
                                        let uu____3388 =
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "list_of_string"] in
                                        (uu____3388, (Prims.parse_int "1"),
                                          (unary_op arg_as_string
                                             list_of_string')) in
                                      let uu____3394 =
                                        let uu____3404 =
                                          let uu____3413 =
                                            FStar_Syntax_Const.p2l
                                              ["FStar";
                                              "String";
                                              "string_of_list"] in
                                          (uu____3413, (Prims.parse_int "1"),
                                            (unary_op
                                               (arg_as_list arg_as_char)
                                               string_of_list')) in
                                        let uu____3420 =
                                          let uu____3430 =
                                            let uu____3442 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar"; "String"; "concat"] in
                                            (uu____3442,
                                              (Prims.parse_int "2"),
                                              string_concat') in
                                          [uu____3430] in
                                        uu____3404 :: uu____3420 in
                                      uu____3379 :: uu____3394 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3369 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3359 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3349 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3339 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3329 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3319 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3309 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3299 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3289 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3279 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3269 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3259 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3249 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3239 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3229 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3219 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3209 in
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
      let uu____3766 =
        let uu____3767 =
          let uu____3768 = FStar_Syntax_Syntax.as_arg c in [uu____3768] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3767 in
      uu____3766 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3792 =
              let uu____3801 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3801, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3810  ->
                        fun uu____3811  ->
                          match (uu____3810, uu____3811) with
                          | ((int_to_t1,x),(uu____3822,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3828 =
              let uu____3838 =
                let uu____3847 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3847, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3856  ->
                          fun uu____3857  ->
                            match (uu____3856, uu____3857) with
                            | ((int_to_t1,x),(uu____3868,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3874 =
                let uu____3884 =
                  let uu____3893 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3893, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3902  ->
                            fun uu____3903  ->
                              match (uu____3902, uu____3903) with
                              | ((int_to_t1,x),(uu____3914,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3884] in
              uu____3838 :: uu____3874 in
            uu____3792 :: uu____3828)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3989)::(a1,uu____3991)::(a2,uu____3993)::[] ->
        let uu____4022 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4022 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____4034 -> None)
    | uu____4035 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____4048)::(a1,uu____4050)::(a2,uu____4052)::[] ->
        let uu____4081 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4081 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4085 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4085.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4085.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4085.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4092 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4092.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4092.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4092.FStar_Syntax_Syntax.vars)
                })
         | uu____4097 -> None)
    | (_typ,uu____4099)::uu____4100::(a1,uu____4102)::(a2,uu____4104)::[] ->
        let uu____4141 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4141 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4145 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4145.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4145.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4145.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4152 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4152.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4152.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4152.FStar_Syntax_Syntax.vars)
                })
         | uu____4157 -> None)
    | uu____4158 -> failwith "Unexpected number of arguments" in
  let decidable_equality =
    [{
       name = FStar_Syntax_Const.op_Eq;
       arity = (Prims.parse_int "3");
       strong_reduction_ok = true;
       interpretation = (interp_bool false)
     };
    {
      name = FStar_Syntax_Const.op_notEq;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = (interp_bool true)
    }] in
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
  FStar_List.append decidable_equality
    [propositional_equality; hetero_propositional_equality]
let reduce_primops:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      let uu____4170 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4170
      then tm
      else
        (let uu____4172 = FStar_Syntax_Util.head_and_args tm in
         match uu____4172 with
         | (head1,args) ->
             let uu____4198 =
               let uu____4199 = FStar_Syntax_Util.un_uinst head1 in
               uu____4199.FStar_Syntax_Syntax.n in
             (match uu____4198 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4203 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4203 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4218 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4218 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4221 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___163_4228 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4228.tcenv);
           delta_level = (uu___163_4228.delta_level);
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
        let uu___164_4250 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4250.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4250.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4250.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4269 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4297 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4297
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4300;
                     FStar_Syntax_Syntax.pos = uu____4301;
                     FStar_Syntax_Syntax.vars = uu____4302;_},uu____4303);
                FStar_Syntax_Syntax.tk = uu____4304;
                FStar_Syntax_Syntax.pos = uu____4305;
                FStar_Syntax_Syntax.vars = uu____4306;_},args)
             ->
             let uu____4326 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4326
             then
               let uu____4327 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4327 with
                | (Some (true ),uu____4360)::(uu____4361,(arg,uu____4363))::[]
                    -> arg
                | (uu____4404,(arg,uu____4406))::(Some (true ),uu____4407)::[]
                    -> arg
                | (Some (false ),uu____4448)::uu____4449::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4487::(Some (false ),uu____4488)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4526 -> tm1)
             else
               (let uu____4536 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4536
                then
                  let uu____4537 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4537 with
                  | (Some (true ),uu____4570)::uu____4571::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4609::(Some (true ),uu____4610)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4648)::(uu____4649,(arg,uu____4651))::[]
                      -> arg
                  | (uu____4692,(arg,uu____4694))::(Some (false ),uu____4695)::[]
                      -> arg
                  | uu____4736 -> tm1
                else
                  (let uu____4746 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4746
                   then
                     let uu____4747 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4747 with
                     | uu____4780::(Some (true ),uu____4781)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4819)::uu____4820::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4858)::(uu____4859,(arg,uu____4861))::[]
                         -> arg
                     | (uu____4902,(p,uu____4904))::(uu____4905,(q,uu____4907))::[]
                         ->
                         let uu____4949 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4949
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4951 -> tm1
                   else
                     (let uu____4961 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4961
                      then
                        let uu____4962 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4962 with
                        | (Some (true ),uu____4995)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5019)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5043 -> tm1
                      else
                        (let uu____5053 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5053
                         then
                           match args with
                           | (t,uu____5055)::[] ->
                               let uu____5068 =
                                 let uu____5069 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5069.FStar_Syntax_Syntax.n in
                               (match uu____5068 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5072::[],body,uu____5074) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5100 -> tm1)
                                | uu____5102 -> tm1)
                           | (uu____5103,Some (FStar_Syntax_Syntax.Implicit
                              uu____5104))::(t,uu____5106)::[] ->
                               let uu____5133 =
                                 let uu____5134 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5134.FStar_Syntax_Syntax.n in
                               (match uu____5133 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5137::[],body,uu____5139) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5165 -> tm1)
                                | uu____5167 -> tm1)
                           | uu____5168 -> tm1
                         else
                           (let uu____5175 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5175
                            then
                              match args with
                              | (t,uu____5177)::[] ->
                                  let uu____5190 =
                                    let uu____5191 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5191.FStar_Syntax_Syntax.n in
                                  (match uu____5190 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5194::[],body,uu____5196) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5222 -> tm1)
                                   | uu____5224 -> tm1)
                              | (uu____5225,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5226))::
                                  (t,uu____5228)::[] ->
                                  let uu____5255 =
                                    let uu____5256 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5256.FStar_Syntax_Syntax.n in
                                  (match uu____5255 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5259::[],body,uu____5261) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5287 -> tm1)
                                   | uu____5289 -> tm1)
                              | uu____5290 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5298;
                FStar_Syntax_Syntax.pos = uu____5299;
                FStar_Syntax_Syntax.vars = uu____5300;_},args)
             ->
             let uu____5316 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5316
             then
               let uu____5317 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5317 with
                | (Some (true ),uu____5350)::(uu____5351,(arg,uu____5353))::[]
                    -> arg
                | (uu____5394,(arg,uu____5396))::(Some (true ),uu____5397)::[]
                    -> arg
                | (Some (false ),uu____5438)::uu____5439::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5477::(Some (false ),uu____5478)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5516 -> tm1)
             else
               (let uu____5526 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5526
                then
                  let uu____5527 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5527 with
                  | (Some (true ),uu____5560)::uu____5561::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5599::(Some (true ),uu____5600)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5638)::(uu____5639,(arg,uu____5641))::[]
                      -> arg
                  | (uu____5682,(arg,uu____5684))::(Some (false ),uu____5685)::[]
                      -> arg
                  | uu____5726 -> tm1
                else
                  (let uu____5736 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5736
                   then
                     let uu____5737 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5737 with
                     | uu____5770::(Some (true ),uu____5771)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5809)::uu____5810::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5848)::(uu____5849,(arg,uu____5851))::[]
                         -> arg
                     | (uu____5892,(p,uu____5894))::(uu____5895,(q,uu____5897))::[]
                         ->
                         let uu____5939 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5939
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5941 -> tm1
                   else
                     (let uu____5951 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5951
                      then
                        let uu____5952 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5952 with
                        | (Some (true ),uu____5985)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____6009)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____6033 -> tm1
                      else
                        (let uu____6043 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____6043
                         then
                           match args with
                           | (t,uu____6045)::[] ->
                               let uu____6058 =
                                 let uu____6059 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6059.FStar_Syntax_Syntax.n in
                               (match uu____6058 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6062::[],body,uu____6064) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6090 -> tm1)
                                | uu____6092 -> tm1)
                           | (uu____6093,Some (FStar_Syntax_Syntax.Implicit
                              uu____6094))::(t,uu____6096)::[] ->
                               let uu____6123 =
                                 let uu____6124 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6124.FStar_Syntax_Syntax.n in
                               (match uu____6123 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6127::[],body,uu____6129) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6155 -> tm1)
                                | uu____6157 -> tm1)
                           | uu____6158 -> tm1
                         else
                           (let uu____6165 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6165
                            then
                              match args with
                              | (t,uu____6167)::[] ->
                                  let uu____6180 =
                                    let uu____6181 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6181.FStar_Syntax_Syntax.n in
                                  (match uu____6180 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6184::[],body,uu____6186) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6212 -> tm1)
                                   | uu____6214 -> tm1)
                              | (uu____6215,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6216))::
                                  (t,uu____6218)::[] ->
                                  let uu____6245 =
                                    let uu____6246 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6246.FStar_Syntax_Syntax.n in
                                  (match uu____6245 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6249::[],body,uu____6251) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6277 -> tm1)
                                   | uu____6279 -> tm1)
                              | uu____6280 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6287 -> tm1)
let is_norm_request hd1 args =
  let uu____6302 =
    let uu____6306 =
      let uu____6307 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6307.FStar_Syntax_Syntax.n in
    (uu____6306, args) in
  match uu____6302 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6312::uu____6313::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6316::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6318 -> false
let get_norm_request args =
  match args with
  | uu____6337::(tm,uu____6339)::[] -> tm
  | (tm,uu____6349)::[] -> tm
  | uu____6354 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6361  ->
    match uu___140_6361 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6363;
           FStar_Syntax_Syntax.pos = uu____6364;
           FStar_Syntax_Syntax.vars = uu____6365;_},uu____6366,uu____6367))::uu____6368
        -> true
    | uu____6374 -> false
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
            (fun uu____6492  ->
               let uu____6493 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6494 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6495 =
                 let uu____6496 =
                   let uu____6498 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6498 in
                 stack_to_string uu____6496 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6493
                 uu____6494 uu____6495);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6510 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6531 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6540 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6541 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6542;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6543;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6548;
                 FStar_Syntax_Syntax.fv_delta = uu____6549;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6553;
                 FStar_Syntax_Syntax.fv_delta = uu____6554;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6555);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (is_fstar_tactics_embed hd1) ||
                 (is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6588 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6588.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6588.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6588.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6614 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6614) && (is_norm_request hd1 args))
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
                 let uu___166_6627 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6627.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6627.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6632;
                  FStar_Syntax_Syntax.pos = uu____6633;
                  FStar_Syntax_Syntax.vars = uu____6634;_},a1::a2::rest)
               ->
               let uu____6668 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6668 with
                | (hd1,uu____6679) ->
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
                    (FStar_Const.Const_reflect uu____6734);
                  FStar_Syntax_Syntax.tk = uu____6735;
                  FStar_Syntax_Syntax.pos = uu____6736;
                  FStar_Syntax_Syntax.vars = uu____6737;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6760 = FStar_List.tl stack1 in
               norm cfg env uu____6760 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6763;
                  FStar_Syntax_Syntax.pos = uu____6764;
                  FStar_Syntax_Syntax.vars = uu____6765;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6788 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6788 with
                | (reify_head,uu____6799) ->
                    let a1 =
                      let uu____6815 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6815 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6818);
                            FStar_Syntax_Syntax.tk = uu____6819;
                            FStar_Syntax_Syntax.pos = uu____6820;
                            FStar_Syntax_Syntax.vars = uu____6821;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6846 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6854 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6854
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6861 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6861
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6864 =
                      let uu____6868 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6868, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6864 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6877  ->
                         match uu___141_6877 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6880 =
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
                 if uu____6880 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6884 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6884 in
                  let uu____6885 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6885 with
                  | None  ->
                      (log cfg
                         (fun uu____6896  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6902  ->
                            let uu____6903 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6904 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6903 uu____6904);
                       (let t3 =
                          let uu____6906 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6906
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
                          | (UnivArgs (us',uu____6922))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6935 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6936 ->
                              let uu____6937 =
                                let uu____6938 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6938 in
                              failwith uu____6937
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6945 = lookup_bvar env x in
               (match uu____6945 with
                | Univ uu____6946 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____6961 = FStar_ST.read r in
                      (match uu____6961 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6980  ->
                                 let uu____6981 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6982 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6981
                                   uu____6982);
                            (let uu____6983 =
                               let uu____6984 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6984.FStar_Syntax_Syntax.n in
                             match uu____6983 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6987 ->
                                 norm cfg env2 stack1 t'
                             | uu____7002 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____7035)::uu____7036 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____7041)::uu____7042 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____7048,uu____7049))::stack_rest ->
                    (match c with
                     | Univ uu____7052 -> norm cfg (c :: env) stack_rest t1
                     | uu____7053 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____7056::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____7069  ->
                                         let uu____7070 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7070);
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
                                           (fun uu___142_7084  ->
                                              match uu___142_7084 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____7085 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7087  ->
                                         let uu____7088 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7088);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____7099  ->
                                         let uu____7100 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7100);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____7101 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7108 ->
                                   let cfg1 =
                                     let uu___167_7116 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_7116.tcenv);
                                       delta_level =
                                         (uu___167_7116.delta_level);
                                       primitive_steps =
                                         (uu___167_7116.primitive_steps)
                                     } in
                                   let uu____7117 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7117)
                          | uu____7118::tl1 ->
                              (log cfg
                                 (fun uu____7128  ->
                                    let uu____7129 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7129);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_7153 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_7153.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7166  ->
                          let uu____7167 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7167);
                     norm cfg env stack2 t1)
                | (Debug uu____7168)::uu____7169 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7171 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7171
                    else
                      (let uu____7173 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7173 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7202 =
                                   let uu____7208 =
                                     let uu____7209 =
                                       let uu____7210 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7210 in
                                     FStar_All.pipe_right uu____7209
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7208
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7202
                                   (fun _0_42  -> Some _0_42)
                             | uu____7235 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7249  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7254  ->
                                 let uu____7255 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7255);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7267 = cfg in
                               let uu____7268 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7267.steps);
                                 tcenv = (uu___169_7267.tcenv);
                                 delta_level = (uu___169_7267.delta_level);
                                 primitive_steps = uu____7268
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7278)::uu____7279 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7283 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7283
                    else
                      (let uu____7285 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7285 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7314 =
                                   let uu____7320 =
                                     let uu____7321 =
                                       let uu____7322 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7322 in
                                     FStar_All.pipe_right uu____7321
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7320
                                     (fun _0_43  -> FStar_Util.Inl _0_43) in
                                 FStar_All.pipe_right uu____7314
                                   (fun _0_44  -> Some _0_44)
                             | uu____7347 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7361  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7366  ->
                                 let uu____7367 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7367);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7379 = cfg in
                               let uu____7380 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7379.steps);
                                 tcenv = (uu___169_7379.tcenv);
                                 delta_level = (uu___169_7379.delta_level);
                                 primitive_steps = uu____7380
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7390)::uu____7391 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7397 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7397
                    else
                      (let uu____7399 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7399 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7428 =
                                   let uu____7434 =
                                     let uu____7435 =
                                       let uu____7436 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7436 in
                                     FStar_All.pipe_right uu____7435
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7434
                                     (fun _0_45  -> FStar_Util.Inl _0_45) in
                                 FStar_All.pipe_right uu____7428
                                   (fun _0_46  -> Some _0_46)
                             | uu____7461 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7475  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7480  ->
                                 let uu____7481 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7481);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7493 = cfg in
                               let uu____7494 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7493.steps);
                                 tcenv = (uu___169_7493.tcenv);
                                 delta_level = (uu___169_7493.delta_level);
                                 primitive_steps = uu____7494
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7504)::uu____7505 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7510 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7510
                    else
                      (let uu____7512 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7512 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7541 =
                                   let uu____7547 =
                                     let uu____7548 =
                                       let uu____7549 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7549 in
                                     FStar_All.pipe_right uu____7548
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7547
                                     (fun _0_47  -> FStar_Util.Inl _0_47) in
                                 FStar_All.pipe_right uu____7541
                                   (fun _0_48  -> Some _0_48)
                             | uu____7574 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7588  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7593  ->
                                 let uu____7594 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7594);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7606 = cfg in
                               let uu____7607 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7606.steps);
                                 tcenv = (uu___169_7606.tcenv);
                                 delta_level = (uu___169_7606.delta_level);
                                 primitive_steps = uu____7607
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7617)::uu____7618 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7628 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7628
                    else
                      (let uu____7630 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7630 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7659 =
                                   let uu____7665 =
                                     let uu____7666 =
                                       let uu____7667 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7667 in
                                     FStar_All.pipe_right uu____7666
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7665
                                     (fun _0_49  -> FStar_Util.Inl _0_49) in
                                 FStar_All.pipe_right uu____7659
                                   (fun _0_50  -> Some _0_50)
                             | uu____7692 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7706  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7711  ->
                                 let uu____7712 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7712);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7724 = cfg in
                               let uu____7725 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7724.steps);
                                 tcenv = (uu___169_7724.tcenv);
                                 delta_level = (uu___169_7724.delta_level);
                                 primitive_steps = uu____7725
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7735 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7735
                    else
                      (let uu____7737 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7737 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7766 =
                                   let uu____7772 =
                                     let uu____7773 =
                                       let uu____7774 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7774 in
                                     FStar_All.pipe_right uu____7773
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7772
                                     (fun _0_51  -> FStar_Util.Inl _0_51) in
                                 FStar_All.pipe_right uu____7766
                                   (fun _0_52  -> Some _0_52)
                             | uu____7799 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7813  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7818  ->
                                 let uu____7819 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7819);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7831 = cfg in
                               let uu____7832 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7831.steps);
                                 tcenv = (uu___169_7831.tcenv);
                                 delta_level = (uu___169_7831.delta_level);
                                 primitive_steps = uu____7832
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
                      (fun uu____7864  ->
                         fun stack2  ->
                           match uu____7864 with
                           | (a,aq) ->
                               let uu____7872 =
                                 let uu____7873 =
                                   let uu____7877 =
                                     let uu____7878 =
                                       let uu____7888 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7888, false) in
                                     Clos uu____7878 in
                                   (uu____7877, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7873 in
                               uu____7872 :: stack2) args) in
               (log cfg
                  (fun uu____7910  ->
                     let uu____7911 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7911);
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
                             ((let uu___170_7934 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7934.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7934.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7935 ->
                      let uu____7938 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7938)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7941 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7941 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7957 =
                          let uu____7958 =
                            let uu____7963 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_7964 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_7964.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_7964.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7963) in
                          FStar_Syntax_Syntax.Tm_refine uu____7958 in
                        mk uu____7957 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____7977 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7977
               else
                 (let uu____7979 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7979 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7985 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7991  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7985 c1 in
                      let t2 =
                        let uu____7998 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7998 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____8041)::uu____8042 -> norm cfg env stack1 t11
                | (Arg uu____8047)::uu____8048 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____8053;
                       FStar_Syntax_Syntax.pos = uu____8054;
                       FStar_Syntax_Syntax.vars = uu____8055;_},uu____8056,uu____8057))::uu____8058
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____8064)::uu____8065 ->
                    norm cfg env stack1 t11
                | uu____8070 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____8073  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____8086 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____8086
                        | FStar_Util.Inr c ->
                            let uu____8094 = norm_comp cfg env c in
                            FStar_Util.Inr uu____8094 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____8099 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____8099)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____8150,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____8151;
                              FStar_Syntax_Syntax.lbunivs = uu____8152;
                              FStar_Syntax_Syntax.lbtyp = uu____8153;
                              FStar_Syntax_Syntax.lbeff = uu____8154;
                              FStar_Syntax_Syntax.lbdef = uu____8155;_}::uu____8156),uu____8157)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8183 =
                 (let uu____8184 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8184) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8185 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8185))) in
               if uu____8183
               then
                 let env1 =
                   let uu____8188 =
                     let uu____8189 =
                       let uu____8199 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8199,
                         false) in
                     Clos uu____8189 in
                   uu____8188 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8223 =
                    let uu____8226 =
                      let uu____8227 =
                        let uu____8228 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8228
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8227] in
                    FStar_Syntax_Subst.open_term uu____8226 body in
                  match uu____8223 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8234 = lb in
                        let uu____8235 =
                          let uu____8238 =
                            let uu____8239 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8239
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8238
                            (fun _0_53  -> FStar_Util.Inl _0_53) in
                        let uu____8248 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8251 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8235;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8234.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8248;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8234.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8251
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8261  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8277 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8277
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8290 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8312  ->
                        match uu____8312 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8351 =
                                let uu___173_8352 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8352.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8352.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8351 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8290 with
                | (rec_env,memos,uu____8412) ->
                    let uu____8427 =
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
                             let uu____8469 =
                               let uu____8470 =
                                 let uu____8480 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8480, false) in
                               Clos uu____8470 in
                             uu____8469 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8518;
                             FStar_Syntax_Syntax.pos = uu____8519;
                             FStar_Syntax_Syntax.vars = uu____8520;_},uu____8521,uu____8522))::uu____8523
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8529 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8536 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8536
                        then
                          let uu___174_8537 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8537.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8537.primitive_steps)
                          }
                        else
                          (let uu___175_8539 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8539.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8539.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8541 =
                         let uu____8542 = FStar_Syntax_Subst.compress head1 in
                         uu____8542.FStar_Syntax_Syntax.n in
                       match uu____8541 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8556 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8556 with
                            | (uu____8557,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8561 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8568 =
                                         let uu____8569 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8569.FStar_Syntax_Syntax.n in
                                       match uu____8568 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8574,uu____8575))
                                           ->
                                           let uu____8584 =
                                             let uu____8585 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8585.FStar_Syntax_Syntax.n in
                                           (match uu____8584 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8590,msrc,uu____8592))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8601 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8601
                                            | uu____8602 -> None)
                                       | uu____8603 -> None in
                                     let uu____8604 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8604 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8608 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8608.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8608.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8608.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8609 =
                                            FStar_List.tl stack1 in
                                          let uu____8610 =
                                            let uu____8611 =
                                              let uu____8614 =
                                                let uu____8615 =
                                                  let uu____8623 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8623) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8615 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8614 in
                                            uu____8611 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8609 uu____8610
                                      | None  ->
                                          let uu____8640 =
                                            let uu____8641 = is_return body in
                                            match uu____8641 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8644;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8645;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8646;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8651 -> false in
                                          if uu____8640
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
                                               let uu____8671 =
                                                 let uu____8674 =
                                                   let uu____8675 =
                                                     let uu____8690 =
                                                       let uu____8692 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8692] in
                                                     (uu____8690, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8675 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8674 in
                                               uu____8671 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8725 =
                                                 let uu____8726 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8726.FStar_Syntax_Syntax.n in
                                               match uu____8725 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8732::uu____8733::[])
                                                   ->
                                                   let uu____8739 =
                                                     let uu____8742 =
                                                       let uu____8743 =
                                                         let uu____8748 =
                                                           let uu____8750 =
                                                             let uu____8751 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8751 in
                                                           let uu____8752 =
                                                             let uu____8754 =
                                                               let uu____8755
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8755 in
                                                             [uu____8754] in
                                                           uu____8750 ::
                                                             uu____8752 in
                                                         (bind1, uu____8748) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8743 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8742 in
                                                   uu____8739 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8767 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8773 =
                                                 let uu____8776 =
                                                   let uu____8777 =
                                                     let uu____8787 =
                                                       let uu____8789 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8790 =
                                                         let uu____8792 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8793 =
                                                           let uu____8795 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8796 =
                                                             let uu____8798 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8799 =
                                                               let uu____8801
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8802
                                                                 =
                                                                 let uu____8804
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8804] in
                                                               uu____8801 ::
                                                                 uu____8802 in
                                                             uu____8798 ::
                                                               uu____8799 in
                                                           uu____8795 ::
                                                             uu____8796 in
                                                         uu____8792 ::
                                                           uu____8793 in
                                                       uu____8789 ::
                                                         uu____8790 in
                                                     (bind_inst, uu____8787) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8777 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8776 in
                                               uu____8773 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8816 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8816 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8834 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8834 with
                            | (uu____8835,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8858 =
                                        let uu____8859 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8859.FStar_Syntax_Syntax.n in
                                      match uu____8858 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8865) -> t4
                                      | uu____8870 -> head2 in
                                    let uu____8871 =
                                      let uu____8872 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8872.FStar_Syntax_Syntax.n in
                                    match uu____8871 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8877 -> None in
                                  let uu____8878 = maybe_extract_fv head2 in
                                  match uu____8878 with
                                  | Some x when
                                      let uu____8884 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8884
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8888 =
                                          maybe_extract_fv head3 in
                                        match uu____8888 with
                                        | Some uu____8891 -> Some true
                                        | uu____8892 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8895 -> (head2, None) in
                                ((let is_arg_impure uu____8906 =
                                    match uu____8906 with
                                    | (e,q) ->
                                        let uu____8911 =
                                          let uu____8912 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8912.FStar_Syntax_Syntax.n in
                                        (match uu____8911 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8927 -> false) in
                                  let uu____8928 =
                                    let uu____8929 =
                                      let uu____8933 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8933 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8929 in
                                  if uu____8928
                                  then
                                    let uu____8936 =
                                      let uu____8937 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8937 in
                                    failwith uu____8936
                                  else ());
                                 (let uu____8939 =
                                    maybe_unfold_action head_app in
                                  match uu____8939 with
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
                                      let uu____8974 = FStar_List.tl stack1 in
                                      norm cfg env uu____8974 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____8988 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8988 in
                           let uu____8989 = FStar_List.tl stack1 in
                           norm cfg env uu____8989 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____9072  ->
                                     match uu____9072 with
                                     | (pat,wopt,tm) ->
                                         let uu____9110 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9110))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9136 = FStar_List.tl stack1 in
                           norm cfg env uu____9136 tm
                       | uu____9137 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9146;
                             FStar_Syntax_Syntax.pos = uu____9147;
                             FStar_Syntax_Syntax.vars = uu____9148;_},uu____9149,uu____9150))::uu____9151
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9157 -> false in
                    if should_reify
                    then
                      let uu____9158 = FStar_List.tl stack1 in
                      let uu____9159 =
                        let uu____9160 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9160 in
                      norm cfg env uu____9158 uu____9159
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9163 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9163
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_9169 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_9169.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_9169.primitive_steps)
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
                | uu____9171 ->
                    (match stack1 with
                     | uu____9172::uu____9173 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9177)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____9192 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9202 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9202
                           | uu____9209 -> m in
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
              let uu____9221 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9221 with
              | (uu____9222,return_repr) ->
                  let return_inst =
                    let uu____9229 =
                      let uu____9230 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9230.FStar_Syntax_Syntax.n in
                    match uu____9229 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9236::[])
                        ->
                        let uu____9242 =
                          let uu____9245 =
                            let uu____9246 =
                              let uu____9251 =
                                let uu____9253 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9253] in
                              (return_tm, uu____9251) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9246 in
                          FStar_Syntax_Syntax.mk uu____9245 in
                        uu____9242 None e.FStar_Syntax_Syntax.pos
                    | uu____9265 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9268 =
                    let uu____9271 =
                      let uu____9272 =
                        let uu____9282 =
                          let uu____9284 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9285 =
                            let uu____9287 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9287] in
                          uu____9284 :: uu____9285 in
                        (return_inst, uu____9282) in
                      FStar_Syntax_Syntax.Tm_app uu____9272 in
                    FStar_Syntax_Syntax.mk uu____9271 in
                  uu____9268 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9300 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9300 with
               | None  ->
                   let uu____9302 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9302
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9303;
                     FStar_TypeChecker_Env.mtarget = uu____9304;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9305;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9316;
                     FStar_TypeChecker_Env.mtarget = uu____9317;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9318;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9336 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9336)
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
                (fun uu____9366  ->
                   match uu____9366 with
                   | (a,imp) ->
                       let uu____9373 = norm cfg env [] a in
                       (uu____9373, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9388 = comp1 in
            let uu____9391 =
              let uu____9392 =
                let uu____9398 = norm cfg env [] t in
                let uu____9399 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9398, uu____9399) in
              FStar_Syntax_Syntax.Total uu____9392 in
            {
              FStar_Syntax_Syntax.n = uu____9391;
              FStar_Syntax_Syntax.tk = (uu___178_9388.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9388.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9388.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9414 = comp1 in
            let uu____9417 =
              let uu____9418 =
                let uu____9424 = norm cfg env [] t in
                let uu____9425 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9424, uu____9425) in
              FStar_Syntax_Syntax.GTotal uu____9418 in
            {
              FStar_Syntax_Syntax.n = uu____9417;
              FStar_Syntax_Syntax.tk = (uu___179_9414.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9414.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9414.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9456  ->
                      match uu____9456 with
                      | (a,i) ->
                          let uu____9463 = norm cfg env [] a in
                          (uu____9463, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9468  ->
                      match uu___143_9468 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9472 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9472
                      | f -> f)) in
            let uu___180_9476 = comp1 in
            let uu____9479 =
              let uu____9480 =
                let uu___181_9481 = ct in
                let uu____9482 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9483 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9486 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9482;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9481.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9483;
                  FStar_Syntax_Syntax.effect_args = uu____9486;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9480 in
            {
              FStar_Syntax_Syntax.n = uu____9479;
              FStar_Syntax_Syntax.tk = (uu___180_9476.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9476.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9476.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9503 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9503.tcenv);
               delta_level = (uu___182_9503.delta_level);
               primitive_steps = (uu___182_9503.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9508 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9508 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9511 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9525 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9525.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9525.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9525.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9535 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9535
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9540 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9540.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9540.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9540.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9540.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9542 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9542.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9542.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9542.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9542.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9543 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9543.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9543.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9543.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9549 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9552  ->
        match uu____9552 with
        | (x,imp) ->
            let uu____9555 =
              let uu___187_9556 = x in
              let uu____9557 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9556.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9556.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9557
              } in
            (uu____9555, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9563 =
          FStar_List.fold_left
            (fun uu____9570  ->
               fun b  ->
                 match uu____9570 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9563 with | (nbs,uu____9587) -> FStar_List.rev nbs
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
            let uu____9604 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9604
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9609 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9609
               then
                 let uu____9613 =
                   let uu____9616 =
                     let uu____9617 =
                       let uu____9620 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9620 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9617 in
                   FStar_Util.Inl uu____9616 in
                 Some uu____9613
               else
                 (let uu____9624 =
                    let uu____9627 =
                      let uu____9628 =
                        let uu____9631 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9631 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9628 in
                    FStar_Util.Inl uu____9627 in
                  Some uu____9624))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9644 -> lopt
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
              ((let uu____9656 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9656
                then
                  let uu____9657 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9658 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9657
                    uu____9658
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9669 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9669.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9689  ->
                    let uu____9690 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9690);
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
              let uu____9727 =
                let uu___189_9728 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9728.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9728.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9728.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9727
          | (Arg (Univ uu____9733,uu____9734,uu____9735))::uu____9736 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9738,uu____9739))::uu____9740 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9752),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9768  ->
                    let uu____9769 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9769);
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
                 (let uu____9780 = FStar_ST.read m in
                  match uu____9780 with
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
                  | Some (uu____9806,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9828 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9828
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9835  ->
                    let uu____9836 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9836);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9841 =
                  log cfg
                    (fun uu____9843  ->
                       let uu____9844 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9845 =
                         let uu____9846 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9853  ->
                                   match uu____9853 with
                                   | (p,uu____9859,uu____9860) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9846
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9844 uu____9845);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9870  ->
                               match uu___144_9870 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9871 -> false)) in
                     let steps' =
                       let uu____9874 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9874
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9877 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9877.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9877.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9911 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9927 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9961  ->
                                   fun uu____9962  ->
                                     match (uu____9961, uu____9962) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____10027 = norm_pat env3 p1 in
                                         (match uu____10027 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9927 with
                          | (pats1,env3) ->
                              ((let uu___191_10093 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_10093.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_10093.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_10107 = x in
                           let uu____10108 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_10107.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_10107.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10108
                           } in
                         ((let uu___193_10114 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_10114.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_10114.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_10119 = x in
                           let uu____10120 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_10119.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_10119.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10120
                           } in
                         ((let uu___195_10126 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_10126.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_10126.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_10136 = x in
                           let uu____10137 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_10136.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_10136.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10137
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_10144 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_10144.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_10144.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10148 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10151 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10151 with
                                 | (p,wopt,e) ->
                                     let uu____10169 = norm_pat env1 p in
                                     (match uu____10169 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10193 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10193 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10198 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10198) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10208) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10213 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10214;
                        FStar_Syntax_Syntax.fv_delta = uu____10215;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10219;
                        FStar_Syntax_Syntax.fv_delta = uu____10220;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10221);_}
                      -> true
                  | uu____10228 -> false in
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
                  let uu____10327 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____10327 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10359 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____10361 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10363 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10375 ->
                                let uu____10376 =
                                  let uu____10377 = is_cons head1 in
                                  Prims.op_Negation uu____10377 in
                                FStar_Util.Inr uu____10376)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10391 =
                             let uu____10392 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10392.FStar_Syntax_Syntax.n in
                           (match uu____10391 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10399 ->
                                let uu____10400 =
                                  let uu____10401 = is_cons head1 in
                                  Prims.op_Negation uu____10401 in
                                FStar_Util.Inr uu____10400))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10435)::rest_a,(p1,uu____10438)::rest_p) ->
                      let uu____10466 = matches_pat t1 p1 in
                      (match uu____10466 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10480 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10551 = matches_pat scrutinee1 p1 in
                      (match uu____10551 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10561  ->
                                 let uu____10562 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10563 =
                                   let uu____10564 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10564
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10562 uu____10563);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10573 =
                                        let uu____10574 =
                                          let uu____10584 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10584, false) in
                                        Clos uu____10574 in
                                      uu____10573 :: env2) env1 s in
                             let uu____10607 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10607))) in
                let uu____10608 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10608
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10622  ->
                match uu___145_10622 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10625 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10629 -> d in
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
            let uu___198_10649 = config s e in
            {
              steps = (uu___198_10649.steps);
              tcenv = (uu___198_10649.tcenv);
              delta_level = (uu___198_10649.delta_level);
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
      fun t  -> let uu____10668 = config s e in norm_comp uu____10668 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10675 = config [] env in norm_universe uu____10675 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10682 = config [] env in ghost_to_pure_aux uu____10682 [] c
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
        let uu____10694 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10694 in
      let uu____10695 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10695
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10697 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10697.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10697.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10698  ->
                    let uu____10699 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10699))
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
            ((let uu____10712 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10712);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10721 = config [AllowUnboundUniverses] env in
          norm_comp uu____10721 [] c
        with
        | e ->
            ((let uu____10725 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10725);
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
                   let uu____10762 =
                     let uu____10763 =
                       let uu____10768 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10768) in
                     FStar_Syntax_Syntax.Tm_refine uu____10763 in
                   mk uu____10762 t01.FStar_Syntax_Syntax.pos
               | uu____10773 -> t2)
          | uu____10774 -> t2 in
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
                        (let uu____10854 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10854 with
                         | (binders,args) ->
                             let uu____10864 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10867 =
                               let uu____10874 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_54  -> FStar_Util.Inl _0_54) in
                               FStar_All.pipe_right uu____10874
                                 (fun _0_55  -> Some _0_55) in
                             FStar_Syntax_Util.abs binders uu____10864
                               uu____10867)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10910 =
        let uu____10914 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10914, (t.FStar_Syntax_Syntax.n)) in
      match uu____10910 with
      | (Some sort,uu____10921) ->
          let uu____10923 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10923
      | (uu____10924,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10928 ->
          let uu____10932 = FStar_Syntax_Util.head_and_args t in
          (match uu____10932 with
           | (head1,args) ->
               let uu____10958 =
                 let uu____10959 = FStar_Syntax_Subst.compress head1 in
                 uu____10959.FStar_Syntax_Syntax.n in
               (match uu____10958 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10962,thead) ->
                    let uu____10976 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10976 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____11011 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_11015 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_11015.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_11015.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_11015.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_11015.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_11015.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_11015.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_11015.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_11015.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_11015.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_11015.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_11015.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_11015.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_11015.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_11015.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_11015.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_11015.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_11015.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_11015.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_11015.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_11015.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_11015.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_11015.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___204_11015.FStar_TypeChecker_Env.synth)
                                 }) t in
                            match uu____11011 with
                            | (uu____11016,ty,uu____11018) ->
                                eta_expand_with_type env t ty))
                | uu____11019 ->
                    let uu____11020 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_11024 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_11024.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_11024.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_11024.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_11024.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_11024.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_11024.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_11024.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_11024.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_11024.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_11024.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_11024.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_11024.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_11024.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_11024.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_11024.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_11024.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_11024.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_11024.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_11024.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_11024.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_11024.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_11024.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___205_11024.FStar_TypeChecker_Env.synth)
                         }) t in
                    (match uu____11020 with
                     | (uu____11025,ty,uu____11027) ->
                         eta_expand_with_type env t ty)))