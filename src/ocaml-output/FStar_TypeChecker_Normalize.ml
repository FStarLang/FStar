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
  let decidable_eq neg rng args =
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) rng in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) rng in
    match args with
    | (_typ,uu____3219)::(a1,uu____3221)::(a2,uu____3223)::[] ->
        let uu____3252 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3252 with
         | FStar_Syntax_Util.Equal  -> Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  -> Some (if neg then tru else fal)
         | uu____3264 -> None)
    | uu____3265 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____3277 =
      let uu____3287 =
        let uu____3297 =
          let uu____3307 =
            let uu____3317 =
              let uu____3327 =
                let uu____3337 =
                  let uu____3347 =
                    let uu____3357 =
                      let uu____3367 =
                        let uu____3377 =
                          let uu____3387 =
                            let uu____3397 =
                              let uu____3407 =
                                let uu____3417 =
                                  let uu____3427 =
                                    let uu____3437 =
                                      let uu____3447 =
                                        let uu____3457 =
                                          let uu____3467 =
                                            let uu____3476 =
                                              FStar_Syntax_Const.p2l
                                                ["FStar";
                                                "String";
                                                "list_of_string"] in
                                            (uu____3476,
                                              (Prims.parse_int "1"),
                                              (unary_op arg_as_string
                                                 list_of_string')) in
                                          let uu____3482 =
                                            let uu____3492 =
                                              let uu____3501 =
                                                FStar_Syntax_Const.p2l
                                                  ["FStar";
                                                  "String";
                                                  "string_of_list"] in
                                              (uu____3501,
                                                (Prims.parse_int "1"),
                                                (unary_op
                                                   (arg_as_list arg_as_char)
                                                   string_of_list')) in
                                            let uu____3508 =
                                              let uu____3518 =
                                                let uu____3530 =
                                                  FStar_Syntax_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "concat"] in
                                                (uu____3530,
                                                  (Prims.parse_int "2"),
                                                  string_concat') in
                                              [uu____3518] in
                                            uu____3492 :: uu____3508 in
                                          uu____3467 :: uu____3482 in
                                        (FStar_Syntax_Const.op_notEq,
                                          (Prims.parse_int "3"),
                                          (decidable_eq true)) :: uu____3457 in
                                      (FStar_Syntax_Const.op_Eq,
                                        (Prims.parse_int "3"),
                                        (decidable_eq false)) :: uu____3447 in
                                    (FStar_Syntax_Const.string_compare,
                                      (Prims.parse_int "2"),
                                      (binary_op arg_as_string
                                         string_compare'))
                                      :: uu____3437 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3427 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3417 in
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____3407 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3397 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3387 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3377 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3367 in
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
                      :: uu____3357 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3347 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3337 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3327 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3317 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3307 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3297 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3287 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3277 in
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
      let uu____3880 =
        let uu____3881 =
          let uu____3882 = FStar_Syntax_Syntax.as_arg c in [uu____3882] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3881 in
      uu____3880 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3906 =
              let uu____3915 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3915, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3924  ->
                        fun uu____3925  ->
                          match (uu____3924, uu____3925) with
                          | ((int_to_t1,x),(uu____3936,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3942 =
              let uu____3952 =
                let uu____3961 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3961, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3970  ->
                          fun uu____3971  ->
                            match (uu____3970, uu____3971) with
                            | ((int_to_t1,x),(uu____3982,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3988 =
                let uu____3998 =
                  let uu____4007 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____4007, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____4016  ->
                            fun uu____4017  ->
                              match (uu____4016, uu____4017) with
                              | ((int_to_t1,x),(uu____4028,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3998] in
              uu____3952 :: uu____3988 in
            uu____3906 :: uu____3942)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop r args =
    match args with
    | (_typ,uu____4094)::(a1,uu____4096)::(a2,uu____4098)::[] ->
        let uu____4127 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4127 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4131 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4131.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4131.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4131.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4138 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4138.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4138.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4138.FStar_Syntax_Syntax.vars)
                })
         | uu____4143 -> None)
    | (_typ,uu____4145)::uu____4146::(a1,uu____4148)::(a2,uu____4150)::[] ->
        let uu____4187 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4187 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___161_4191 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___161_4191.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___161_4191.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___161_4191.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___162_4198 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_4198.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___162_4198.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___162_4198.FStar_Syntax_Syntax.vars)
                })
         | uu____4203 -> None)
    | uu____4204 -> failwith "Unexpected number of arguments" in
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
      let uu____4214 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____4214
      then tm
      else
        (let uu____4216 = FStar_Syntax_Util.head_and_args tm in
         match uu____4216 with
         | (head1,args) ->
             let uu____4242 =
               let uu____4243 = FStar_Syntax_Util.un_uinst head1 in
               uu____4243.FStar_Syntax_Syntax.n in
             (match uu____4242 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____4247 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____4247 with
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
                         (let uu____4262 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4262 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4265 -> tm))
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___163_4272 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___163_4272.tcenv);
           delta_level = (uu___163_4272.delta_level);
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
        let uu___164_4294 = t in
        {
          FStar_Syntax_Syntax.n = (uu___164_4294.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___164_4294.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___164_4294.FStar_Syntax_Syntax.vars)
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
        | uu____4313 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let tm1 = reduce_primops cfg tm in
      let uu____4341 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4341
      then tm1
      else
        (match tm1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.tk = uu____4344;
                     FStar_Syntax_Syntax.pos = uu____4345;
                     FStar_Syntax_Syntax.vars = uu____4346;_},uu____4347);
                FStar_Syntax_Syntax.tk = uu____4348;
                FStar_Syntax_Syntax.pos = uu____4349;
                FStar_Syntax_Syntax.vars = uu____4350;_},args)
             ->
             let uu____4370 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4370
             then
               let uu____4371 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4371 with
                | (Some (true ),uu____4404)::(uu____4405,(arg,uu____4407))::[]
                    -> arg
                | (uu____4448,(arg,uu____4450))::(Some (true ),uu____4451)::[]
                    -> arg
                | (Some (false ),uu____4492)::uu____4493::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4531::(Some (false ),uu____4532)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4570 -> tm1)
             else
               (let uu____4580 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4580
                then
                  let uu____4581 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4581 with
                  | (Some (true ),uu____4614)::uu____4615::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4653::(Some (true ),uu____4654)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4692)::(uu____4693,(arg,uu____4695))::[]
                      -> arg
                  | (uu____4736,(arg,uu____4738))::(Some (false ),uu____4739)::[]
                      -> arg
                  | uu____4780 -> tm1
                else
                  (let uu____4790 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4790
                   then
                     let uu____4791 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4791 with
                     | uu____4824::(Some (true ),uu____4825)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4863)::uu____4864::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4902)::(uu____4903,(arg,uu____4905))::[]
                         -> arg
                     | (uu____4946,(p,uu____4948))::(uu____4949,(q,uu____4951))::[]
                         ->
                         let uu____4993 = FStar_Syntax_Util.term_eq p q in
                         (if uu____4993
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____4995 -> tm1
                   else
                     (let uu____5005 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5005
                      then
                        let uu____5006 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5006 with
                        | (Some (true ),uu____5039)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5063)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5087 -> tm1
                      else
                        (let uu____5097 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5097
                         then
                           match args with
                           | (t,uu____5099)::[] ->
                               let uu____5112 =
                                 let uu____5113 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5113.FStar_Syntax_Syntax.n in
                               (match uu____5112 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5116::[],body,uu____5118) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5144 -> tm1)
                                | uu____5146 -> tm1)
                           | (uu____5147,Some (FStar_Syntax_Syntax.Implicit
                              uu____5148))::(t,uu____5150)::[] ->
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
                           | uu____5212 -> tm1
                         else
                           (let uu____5219 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5219
                            then
                              match args with
                              | (t,uu____5221)::[] ->
                                  let uu____5234 =
                                    let uu____5235 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5235.FStar_Syntax_Syntax.n in
                                  (match uu____5234 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5238::[],body,uu____5240) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5266 -> tm1)
                                   | uu____5268 -> tm1)
                              | (uu____5269,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5270))::
                                  (t,uu____5272)::[] ->
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
                              | uu____5334 -> tm1
                            else reduce_equality cfg tm1)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5342;
                FStar_Syntax_Syntax.pos = uu____5343;
                FStar_Syntax_Syntax.vars = uu____5344;_},args)
             ->
             let uu____5360 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5360
             then
               let uu____5361 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5361 with
                | (Some (true ),uu____5394)::(uu____5395,(arg,uu____5397))::[]
                    -> arg
                | (uu____5438,(arg,uu____5440))::(Some (true ),uu____5441)::[]
                    -> arg
                | (Some (false ),uu____5482)::uu____5483::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5521::(Some (false ),uu____5522)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5560 -> tm1)
             else
               (let uu____5570 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5570
                then
                  let uu____5571 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5571 with
                  | (Some (true ),uu____5604)::uu____5605::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5643::(Some (true ),uu____5644)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5682)::(uu____5683,(arg,uu____5685))::[]
                      -> arg
                  | (uu____5726,(arg,uu____5728))::(Some (false ),uu____5729)::[]
                      -> arg
                  | uu____5770 -> tm1
                else
                  (let uu____5780 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5780
                   then
                     let uu____5781 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5781 with
                     | uu____5814::(Some (true ),uu____5815)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5853)::uu____5854::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5892)::(uu____5893,(arg,uu____5895))::[]
                         -> arg
                     | (uu____5936,(p,uu____5938))::(uu____5939,(q,uu____5941))::[]
                         ->
                         let uu____5983 = FStar_Syntax_Util.term_eq p q in
                         (if uu____5983
                          then w FStar_Syntax_Util.t_true
                          else tm1)
                     | uu____5985 -> tm1
                   else
                     (let uu____5995 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5995
                      then
                        let uu____5996 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5996 with
                        | (Some (true ),uu____6029)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____6053)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____6077 -> tm1
                      else
                        (let uu____6087 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____6087
                         then
                           match args with
                           | (t,uu____6089)::[] ->
                               let uu____6102 =
                                 let uu____6103 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____6103.FStar_Syntax_Syntax.n in
                               (match uu____6102 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6106::[],body,uu____6108) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____6134 -> tm1)
                                | uu____6136 -> tm1)
                           | (uu____6137,Some (FStar_Syntax_Syntax.Implicit
                              uu____6138))::(t,uu____6140)::[] ->
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
                           | uu____6202 -> tm1
                         else
                           (let uu____6209 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____6209
                            then
                              match args with
                              | (t,uu____6211)::[] ->
                                  let uu____6224 =
                                    let uu____6225 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6225.FStar_Syntax_Syntax.n in
                                  (match uu____6224 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6228::[],body,uu____6230) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____6256 -> tm1)
                                   | uu____6258 -> tm1)
                              | (uu____6259,Some
                                 (FStar_Syntax_Syntax.Implicit uu____6260))::
                                  (t,uu____6262)::[] ->
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
                              | uu____6324 -> tm1
                            else reduce_equality cfg tm1)))))
         | uu____6331 -> tm1)
let is_norm_request hd1 args =
  let uu____6346 =
    let uu____6350 =
      let uu____6351 = FStar_Syntax_Util.un_uinst hd1 in
      uu____6351.FStar_Syntax_Syntax.n in
    (uu____6350, args) in
  match uu____6346 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6356::uu____6357::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6360::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6362 -> false
let get_norm_request args =
  match args with
  | uu____6381::(tm,uu____6383)::[] -> tm
  | (tm,uu____6393)::[] -> tm
  | uu____6398 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___140_6405  ->
    match uu___140_6405 with
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
           FStar_Syntax_Syntax.tk = uu____6407;
           FStar_Syntax_Syntax.pos = uu____6408;
           FStar_Syntax_Syntax.vars = uu____6409;_},uu____6410,uu____6411))::uu____6412
        -> true
    | uu____6418 -> false
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
            (fun uu____6536  ->
               let uu____6537 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6538 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6539 =
                 let uu____6540 =
                   let uu____6542 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6542 in
                 stack_to_string uu____6540 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6537
                 uu____6538 uu____6539);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6554 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6575 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6584 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6585 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6586;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6587;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6592;
                 FStar_Syntax_Syntax.fv_delta = uu____6593;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6597;
                 FStar_Syntax_Syntax.fv_delta = uu____6598;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6599);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (is_fstar_tactics_embed hd1) ||
                 (is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___165_6632 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.tk =
                     (uu___165_6632.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___165_6632.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___165_6632.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6658 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6658) && (is_norm_request hd1 args))
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
                 let uu___166_6671 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___166_6671.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___166_6671.primitive_steps)
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
                  FStar_Syntax_Syntax.tk = uu____6676;
                  FStar_Syntax_Syntax.pos = uu____6677;
                  FStar_Syntax_Syntax.vars = uu____6678;_},a1::a2::rest)
               ->
               let uu____6712 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6712 with
                | (hd1,uu____6723) ->
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
                    (FStar_Const.Const_reflect uu____6778);
                  FStar_Syntax_Syntax.tk = uu____6779;
                  FStar_Syntax_Syntax.pos = uu____6780;
                  FStar_Syntax_Syntax.vars = uu____6781;_},a::[])
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
               let uu____6804 = FStar_List.tl stack1 in
               norm cfg env uu____6804 (fst a)
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
                  FStar_Syntax_Syntax.tk = uu____6807;
                  FStar_Syntax_Syntax.pos = uu____6808;
                  FStar_Syntax_Syntax.vars = uu____6809;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6832 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6832 with
                | (reify_head,uu____6843) ->
                    let a1 =
                      let uu____6859 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6859 in
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
                              (FStar_Const.Const_reflect uu____6862);
                            FStar_Syntax_Syntax.tk = uu____6863;
                            FStar_Syntax_Syntax.pos = uu____6864;
                            FStar_Syntax_Syntax.vars = uu____6865;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6890 ->
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____6898 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6898
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6905 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6905
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6908 =
                      let uu____6912 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6912, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6908 in
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___141_6921  ->
                         match uu___141_6921 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____6924 =
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
                 if uu____6924 then false else should_delta in
               if Prims.op_Negation should_delta1
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
                    let uu____6928 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6928 in
                  let uu____6929 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6929 with
                  | None  ->
                      (log cfg
                         (fun uu____6940  ->
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
                         (fun uu____6946  ->
                            let uu____6947 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6948 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6947 uu____6948);
                       (let t3 =
                          let uu____6950 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
                          if uu____6950
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
                          | (UnivArgs (us',uu____6966))::stack2 ->
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
                          | uu____6979 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6980 ->
                              let uu____6981 =
                                let uu____6982 =
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
                                  uu____6982 in
                              failwith uu____6981
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6989 = lookup_bvar env x in
               (match uu____6989 with
                | Univ uu____6990 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____7005 = FStar_ST.read r in
                      (match uu____7005 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____7024  ->
                                 let uu____7025 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____7026 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____7025
                                   uu____7026);
                            (let uu____7027 =
                               let uu____7028 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____7028.FStar_Syntax_Syntax.n in
                             match uu____7027 with
                             | FStar_Syntax_Syntax.Tm_abs uu____7031 ->
                                 norm cfg env2 stack1 t'
                             | uu____7046 -> rebuild cfg env2 stack1 t'))
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____7079)::uu____7080 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____7085)::uu____7086 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____7092,uu____7093))::stack_rest ->
                    (match c with
                     | Univ uu____7096 -> norm cfg (c :: env) stack_rest t1
                     | uu____7097 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____7100::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____7113  ->
                                         let uu____7114 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7114);
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
                                           (fun uu___142_7128  ->
                                              match uu___142_7128 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____7129 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____7131  ->
                                         let uu____7132 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7132);
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
                                      (fun uu____7143  ->
                                         let uu____7144 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____7144);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____7145 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____7152 ->
                                   let cfg1 =
                                     let uu___167_7160 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___167_7160.tcenv);
                                       delta_level =
                                         (uu___167_7160.delta_level);
                                       primitive_steps =
                                         (uu___167_7160.primitive_steps)
                                     } in
                                   let uu____7161 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____7161)
                          | uu____7162::tl1 ->
                              (log cfg
                                 (fun uu____7172  ->
                                    let uu____7173 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____7173);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
                      (let uu___168_7197 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___168_7197.tcenv);
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
                       (fun uu____7210  ->
                          let uu____7211 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____7211);
                     norm cfg env stack2 t1)
                | (Debug uu____7212)::uu____7213 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7215 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7215
                    else
                      (let uu____7217 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7217 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7246 =
                                   let uu____7252 =
                                     let uu____7253 =
                                       let uu____7254 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7254 in
                                     FStar_All.pipe_right uu____7253
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7252
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7246
                                   (fun _0_42  -> Some _0_42)
                             | uu____7279 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7293  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7298  ->
                                 let uu____7299 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7299);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7311 = cfg in
                               let uu____7312 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7311.steps);
                                 tcenv = (uu___169_7311.tcenv);
                                 delta_level = (uu___169_7311.delta_level);
                                 primitive_steps = uu____7312
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____7322)::uu____7323 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7327 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7327
                    else
                      (let uu____7329 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7329 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7358 =
                                   let uu____7364 =
                                     let uu____7365 =
                                       let uu____7366 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7366 in
                                     FStar_All.pipe_right uu____7365
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7364
                                     (fun _0_43  -> FStar_Util.Inl _0_43) in
                                 FStar_All.pipe_right uu____7358
                                   (fun _0_44  -> Some _0_44)
                             | uu____7391 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7405  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7410  ->
                                 let uu____7411 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7411);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7423 = cfg in
                               let uu____7424 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7423.steps);
                                 tcenv = (uu___169_7423.tcenv);
                                 delta_level = (uu___169_7423.delta_level);
                                 primitive_steps = uu____7424
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____7434)::uu____7435 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7441 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7441
                    else
                      (let uu____7443 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7443 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7472 =
                                   let uu____7478 =
                                     let uu____7479 =
                                       let uu____7480 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7480 in
                                     FStar_All.pipe_right uu____7479
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7478
                                     (fun _0_45  -> FStar_Util.Inl _0_45) in
                                 FStar_All.pipe_right uu____7472
                                   (fun _0_46  -> Some _0_46)
                             | uu____7505 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7519  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7524  ->
                                 let uu____7525 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7525);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7537 = cfg in
                               let uu____7538 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7537.steps);
                                 tcenv = (uu___169_7537.tcenv);
                                 delta_level = (uu___169_7537.delta_level);
                                 primitive_steps = uu____7538
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____7548)::uu____7549 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7554 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7554
                    else
                      (let uu____7556 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7556 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7585 =
                                   let uu____7591 =
                                     let uu____7592 =
                                       let uu____7593 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7593 in
                                     FStar_All.pipe_right uu____7592
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7591
                                     (fun _0_47  -> FStar_Util.Inl _0_47) in
                                 FStar_All.pipe_right uu____7585
                                   (fun _0_48  -> Some _0_48)
                             | uu____7618 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7632  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7637  ->
                                 let uu____7638 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7638);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7650 = cfg in
                               let uu____7651 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7650.steps);
                                 tcenv = (uu___169_7650.tcenv);
                                 delta_level = (uu___169_7650.delta_level);
                                 primitive_steps = uu____7651
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____7661)::uu____7662 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7672 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7672
                    else
                      (let uu____7674 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7674 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7703 =
                                   let uu____7709 =
                                     let uu____7710 =
                                       let uu____7711 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7711 in
                                     FStar_All.pipe_right uu____7710
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7709
                                     (fun _0_49  -> FStar_Util.Inl _0_49) in
                                 FStar_All.pipe_right uu____7703
                                   (fun _0_50  -> Some _0_50)
                             | uu____7736 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7750  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7755  ->
                                 let uu____7756 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7756);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7768 = cfg in
                               let uu____7769 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7768.steps);
                                 tcenv = (uu___169_7768.tcenv);
                                 delta_level = (uu___169_7768.delta_level);
                                 primitive_steps = uu____7769
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7779 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7779
                    else
                      (let uu____7781 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7781 with
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
                                 let uu____7810 =
                                   let uu____7816 =
                                     let uu____7817 =
                                       let uu____7818 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7818 in
                                     FStar_All.pipe_right uu____7817
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7816
                                     (fun _0_51  -> FStar_Util.Inl _0_51) in
                                 FStar_All.pipe_right uu____7810
                                   (fun _0_52  -> Some _0_52)
                             | uu____7843 -> lopt in
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____7857  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7862  ->
                                 let uu____7863 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____7863);
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
                               let uu___169_7875 = cfg in
                               let uu____7876 =
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
                                 steps = (uu___169_7875.steps);
                                 tcenv = (uu___169_7875.tcenv);
                                 delta_level = (uu___169_7875.delta_level);
                                 primitive_steps = uu____7876
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
                      (fun uu____7908  ->
                         fun stack2  ->
                           match uu____7908 with
                           | (a,aq) ->
                               let uu____7916 =
                                 let uu____7917 =
                                   let uu____7921 =
                                     let uu____7922 =
                                       let uu____7932 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7932, false) in
                                     Clos uu____7922 in
                                   (uu____7921, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7917 in
                               uu____7916 :: stack2) args) in
               (log cfg
                  (fun uu____7954  ->
                     let uu____7955 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7955);
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
                             ((let uu___170_7978 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___170_7978.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___170_7978.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7979 ->
                      let uu____7982 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7982)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7985 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7985 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____8001 =
                          let uu____8002 =
                            let uu____8007 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___171_8008 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___171_8008.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___171_8008.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____8007) in
                          FStar_Syntax_Syntax.Tm_refine uu____8002 in
                        mk uu____8001 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
                 let uu____8021 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____8021
               else
                 (let uu____8023 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____8023 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____8029 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____8035  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____8029 c1 in
                      let t2 =
                        let uu____8042 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____8042 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____8085)::uu____8086 -> norm cfg env stack1 t11
                | (Arg uu____8091)::uu____8092 -> norm cfg env stack1 t11
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.tk = uu____8097;
                       FStar_Syntax_Syntax.pos = uu____8098;
                       FStar_Syntax_Syntax.vars = uu____8099;_},uu____8100,uu____8101))::uu____8102
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____8108)::uu____8109 ->
                    norm cfg env stack1 t11
                | uu____8114 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____8117  ->
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
                            let uu____8130 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____8130
                        | FStar_Util.Inr c ->
                            let uu____8138 = norm_comp cfg env c in
                            FStar_Util.Inr uu____8138 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____8143 =
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 uu____8143)))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
               ((uu____8194,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____8195;
                              FStar_Syntax_Syntax.lbunivs = uu____8196;
                              FStar_Syntax_Syntax.lbtyp = uu____8197;
                              FStar_Syntax_Syntax.lbeff = uu____8198;
                              FStar_Syntax_Syntax.lbdef = uu____8199;_}::uu____8200),uu____8201)
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____8227 =
                 (let uu____8228 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____8228) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____8229 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____8229))) in
               if uu____8227
               then
                 let env1 =
                   let uu____8232 =
                     let uu____8233 =
                       let uu____8243 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____8243,
                         false) in
                     Clos uu____8233 in
                   uu____8232 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____8267 =
                    let uu____8270 =
                      let uu____8271 =
                        let uu____8272 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____8272
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____8271] in
                    FStar_Syntax_Subst.open_term uu____8270 body in
                  match uu____8267 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___172_8278 = lb in
                        let uu____8279 =
                          let uu____8282 =
                            let uu____8283 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____8283
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____8282
                            (fun _0_53  -> FStar_Util.Inl _0_53) in
                        let uu____8292 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____8295 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____8279;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___172_8278.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____8292;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___172_8278.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____8295
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
                             (fun env1  -> fun uu____8305  -> Dummy :: env1)
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____8321 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____8321
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____8334 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8356  ->
                        match uu____8356 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8395 =
                                let uu___173_8396 =
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___173_8396.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___173_8396.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8395 in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____8334 with
                | (rec_env,memos,uu____8456) ->
                    let uu____8471 =
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
                             let uu____8513 =
                               let uu____8514 =
                                 let uu____8524 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8524, false) in
                               Clos uu____8514 in
                             uu____8513 :: env1) (snd lbs) env in
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
                             FStar_Syntax_Syntax.tk = uu____8562;
                             FStar_Syntax_Syntax.pos = uu____8563;
                             FStar_Syntax_Syntax.vars = uu____8564;_},uu____8565,uu____8566))::uu____8567
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8573 -> false in
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
                        let uu____8580 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8580
                        then
                          let uu___174_8581 = cfg in
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
                            tcenv = (uu___174_8581.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___174_8581.primitive_steps)
                          }
                        else
                          (let uu___175_8583 = cfg in
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
                             tcenv = (uu___175_8583.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___175_8583.primitive_steps)
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
                      (let uu____8585 =
                         let uu____8586 = FStar_Syntax_Subst.compress head1 in
                         uu____8586.FStar_Syntax_Syntax.n in
                       match uu____8585 with
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8600 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8600 with
                            | (uu____8601,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8605 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____8612 =
                                         let uu____8613 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8613.FStar_Syntax_Syntax.n in
                                       match uu____8612 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8618,uu____8619))
                                           ->
                                           let uu____8628 =
                                             let uu____8629 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8629.FStar_Syntax_Syntax.n in
                                           (match uu____8628 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8634,msrc,uu____8636))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____8645 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8645
                                            | uu____8646 -> None)
                                       | uu____8647 -> None in
                                     let uu____8648 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8648 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___176_8652 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___176_8652.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___176_8652.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___176_8652.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
                                          let uu____8653 =
                                            FStar_List.tl stack1 in
                                          let uu____8654 =
                                            let uu____8655 =
                                              let uu____8658 =
                                                let uu____8659 =
                                                  let uu____8667 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8667) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8659 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8658 in
                                            uu____8655 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8653 uu____8654
                                      | None  ->
                                          let uu____8684 =
                                            let uu____8685 = is_return body in
                                            match uu____8685 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____8688;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8689;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8690;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8695 -> false in
                                          if uu____8684
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
                                               let uu____8715 =
                                                 let uu____8718 =
                                                   let uu____8719 =
                                                     let uu____8734 =
                                                       let uu____8736 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8736] in
                                                     (uu____8734, body1,
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
                                                     uu____8719 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8718 in
                                               uu____8715 None
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
                                               let uu____8769 =
                                                 let uu____8770 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8770.FStar_Syntax_Syntax.n in
                                               match uu____8769 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8776::uu____8777::[])
                                                   ->
                                                   let uu____8783 =
                                                     let uu____8786 =
                                                       let uu____8787 =
                                                         let uu____8792 =
                                                           let uu____8794 =
                                                             let uu____8795 =
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
                                                               uu____8795 in
                                                           let uu____8796 =
                                                             let uu____8798 =
                                                               let uu____8799
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8799 in
                                                             [uu____8798] in
                                                           uu____8794 ::
                                                             uu____8796 in
                                                         (bind1, uu____8792) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8787 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8786 in
                                                   uu____8783 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8811 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8817 =
                                                 let uu____8820 =
                                                   let uu____8821 =
                                                     let uu____8831 =
                                                       let uu____8833 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8834 =
                                                         let uu____8836 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8837 =
                                                           let uu____8839 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8840 =
                                                             let uu____8842 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8843 =
                                                               let uu____8845
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8846
                                                                 =
                                                                 let uu____8848
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8848] in
                                                               uu____8845 ::
                                                                 uu____8846 in
                                                             uu____8842 ::
                                                               uu____8843 in
                                                           uu____8839 ::
                                                             uu____8840 in
                                                         uu____8836 ::
                                                           uu____8837 in
                                                       uu____8833 ::
                                                         uu____8834 in
                                                     (bind_inst, uu____8831) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8821 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8820 in
                                               uu____8817 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8860 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8860 reified))))
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
                           let uu____8878 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8878 with
                            | (uu____8879,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8902 =
                                        let uu____8903 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8903.FStar_Syntax_Syntax.n in
                                      match uu____8902 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8909) -> t4
                                      | uu____8914 -> head2 in
                                    let uu____8915 =
                                      let uu____8916 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8916.FStar_Syntax_Syntax.n in
                                    match uu____8915 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8921 -> None in
                                  let uu____8922 = maybe_extract_fv head2 in
                                  match uu____8922 with
                                  | Some x when
                                      let uu____8928 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8928
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8932 =
                                          maybe_extract_fv head3 in
                                        match uu____8932 with
                                        | Some uu____8935 -> Some true
                                        | uu____8936 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8939 -> (head2, None) in
                                ((let is_arg_impure uu____8950 =
                                    match uu____8950 with
                                    | (e,q) ->
                                        let uu____8955 =
                                          let uu____8956 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8956.FStar_Syntax_Syntax.n in
                                        (match uu____8955 with
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
                                         | uu____8971 -> false) in
                                  let uu____8972 =
                                    let uu____8973 =
                                      let uu____8977 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8977 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8973 in
                                  if uu____8972
                                  then
                                    let uu____8980 =
                                      let uu____8981 =
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                        uu____8981 in
                                    failwith uu____8980
                                  else ());
                                 (let uu____8983 =
                                    maybe_unfold_action head_app in
                                  match uu____8983 with
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
                                      let uu____9018 = FStar_List.tl stack1 in
                                      norm cfg env uu____9018 body1)))
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
                             let uu____9032 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____9032 in
                           let uu____9033 = FStar_List.tl stack1 in
                           norm cfg env uu____9033 lifted
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun uu____9116  ->
                                     match uu____9116 with
                                     | (pat,wopt,tm) ->
                                         let uu____9154 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____9154))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____9180 = FStar_List.tl stack1 in
                           norm cfg env uu____9180 tm
                       | uu____9181 -> norm cfg env stack1 head1)
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
                             FStar_Syntax_Syntax.tk = uu____9190;
                             FStar_Syntax_Syntax.pos = uu____9191;
                             FStar_Syntax_Syntax.vars = uu____9192;_},uu____9193,uu____9194))::uu____9195
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____9201 -> false in
                    if should_reify
                    then
                      let uu____9202 = FStar_List.tl stack1 in
                      let uu____9203 =
                        let uu____9204 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____9204 in
                      norm cfg env uu____9202 uu____9203
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____9207 =
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
                       if uu____9207
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
                           let uu___177_9213 = cfg in
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
                             tcenv = (uu___177_9213.tcenv);
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
                               (uu___177_9213.primitive_steps)
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
                | uu____9215 ->
                    (match stack1 with
                     | uu____9216::uu____9217 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____9221)
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
                          | uu____9236 -> norm cfg env stack1 head1)
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
                               let uu____9246 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____9246
                           | uu____9253 -> m in
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
              let uu____9265 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____9265 with
              | (uu____9266,return_repr) ->
                  let return_inst =
                    let uu____9273 =
                      let uu____9274 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____9274.FStar_Syntax_Syntax.n in
                    match uu____9273 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____9280::[])
                        ->
                        let uu____9286 =
                          let uu____9289 =
                            let uu____9290 =
                              let uu____9295 =
                                let uu____9297 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____9297] in
                              (return_tm, uu____9295) in
                            FStar_Syntax_Syntax.Tm_uinst uu____9290 in
                          FStar_Syntax_Syntax.mk uu____9289 in
                        uu____9286 None e.FStar_Syntax_Syntax.pos
                    | uu____9309 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____9312 =
                    let uu____9315 =
                      let uu____9316 =
                        let uu____9326 =
                          let uu____9328 = FStar_Syntax_Syntax.as_arg t in
                          let uu____9329 =
                            let uu____9331 = FStar_Syntax_Syntax.as_arg e in
                            [uu____9331] in
                          uu____9328 :: uu____9329 in
                        (return_inst, uu____9326) in
                      FStar_Syntax_Syntax.Tm_app uu____9316 in
                    FStar_Syntax_Syntax.mk uu____9315 in
                  uu____9312 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____9344 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____9344 with
               | None  ->
                   let uu____9346 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____9346
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9347;
                     FStar_TypeChecker_Env.mtarget = uu____9348;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9349;
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
                   { FStar_TypeChecker_Env.msource = uu____9360;
                     FStar_TypeChecker_Env.mtarget = uu____9361;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9362;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9380 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9380)
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
                (fun uu____9410  ->
                   match uu____9410 with
                   | (a,imp) ->
                       let uu____9417 = norm cfg env [] a in
                       (uu____9417, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___178_9432 = comp1 in
            let uu____9435 =
              let uu____9436 =
                let uu____9442 = norm cfg env [] t in
                let uu____9443 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9442, uu____9443) in
              FStar_Syntax_Syntax.Total uu____9436 in
            {
              FStar_Syntax_Syntax.n = uu____9435;
              FStar_Syntax_Syntax.tk = (uu___178_9432.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9432.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9432.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___179_9458 = comp1 in
            let uu____9461 =
              let uu____9462 =
                let uu____9468 = norm cfg env [] t in
                let uu____9469 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9468, uu____9469) in
              FStar_Syntax_Syntax.GTotal uu____9462 in
            {
              FStar_Syntax_Syntax.n = uu____9461;
              FStar_Syntax_Syntax.tk = (uu___179_9458.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___179_9458.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___179_9458.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____9500  ->
                      match uu____9500 with
                      | (a,i) ->
                          let uu____9507 = norm cfg env [] a in
                          (uu____9507, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___143_9512  ->
                      match uu___143_9512 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9516 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9516
                      | f -> f)) in
            let uu___180_9520 = comp1 in
            let uu____9523 =
              let uu____9524 =
                let uu___181_9525 = ct in
                let uu____9526 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9527 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9530 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9526;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___181_9525.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9527;
                  FStar_Syntax_Syntax.effect_args = uu____9530;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9524 in
            {
              FStar_Syntax_Syntax.n = uu____9523;
              FStar_Syntax_Syntax.tk = (uu___180_9520.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9520.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9520.FStar_Syntax_Syntax.vars)
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
            (let uu___182_9547 = cfg in
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
               tcenv = (uu___182_9547.tcenv);
               delta_level = (uu___182_9547.delta_level);
               primitive_steps = (uu___182_9547.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9552 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9552 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9555 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___183_9569 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___183_9569.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___183_9569.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___183_9569.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
            let uu____9579 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9579
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
                    let uu___184_9584 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___184_9584.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___184_9584.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___184_9584.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___184_9584.FStar_Syntax_Syntax.flags)
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                    let uu___185_9586 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___185_9586.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___185_9586.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___185_9586.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___185_9586.FStar_Syntax_Syntax.flags)
                    } in
              let uu___186_9587 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___186_9587.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___186_9587.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___186_9587.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9593 -> c
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
      fun uu____9596  ->
        match uu____9596 with
        | (x,imp) ->
            let uu____9599 =
              let uu___187_9600 = x in
              let uu____9601 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___187_9600.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___187_9600.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9601
              } in
            (uu____9599, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____9607 =
          FStar_List.fold_left
            (fun uu____9614  ->
               fun b  ->
                 match uu____9614 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9607 with | (nbs,uu____9631) -> FStar_List.rev nbs
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
            let uu____9648 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9648
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9653 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9653
               then
                 let uu____9657 =
                   let uu____9660 =
                     let uu____9661 =
                       let uu____9664 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9664 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9661 in
                   FStar_Util.Inl uu____9660 in
                 Some uu____9657
               else
                 (let uu____9668 =
                    let uu____9671 =
                      let uu____9672 =
                        let uu____9675 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9675 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9672 in
                    FStar_Util.Inl uu____9671 in
                  Some uu____9668))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9688 -> lopt
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
              ((let uu____9700 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9700
                then
                  let uu____9701 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9702 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9701
                    uu____9702
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
                (let uu___188_9713 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___188_9713.tcenv);
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
                 (fun uu____9733  ->
                    let uu____9734 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9734);
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
              let uu____9771 =
                let uu___189_9772 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___189_9772.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___189_9772.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___189_9772.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9771
          | (Arg (Univ uu____9777,uu____9778,uu____9779))::uu____9780 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9782,uu____9783))::uu____9784 ->
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
          | (Arg (Clos (env1,tm,m,uu____9796),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9812  ->
                    let uu____9813 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9813);
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
                 (let uu____9824 = FStar_ST.read m in
                  match uu____9824 with
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
                  | Some (uu____9850,a) ->
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
              let uu____9872 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9872
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9879  ->
                    let uu____9880 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9880);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9885 =
                  log cfg
                    (fun uu____9887  ->
                       let uu____9888 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9889 =
                         let uu____9890 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9897  ->
                                   match uu____9897 with
                                   | (p,uu____9903,uu____9904) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9890
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9888 uu____9889);
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
                            (fun uu___144_9914  ->
                               match uu___144_9914 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9915 -> false)) in
                     let steps' =
                       let uu____9918 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9918
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___190_9921 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___190_9921.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___190_9921.primitive_steps)
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_constant uu____9955 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9971 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____10005  ->
                                   fun uu____10006  ->
                                     match (uu____10005, uu____10006) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____10071 = norm_pat env3 p1 in
                                         (match uu____10071 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9971 with
                          | (pats1,env3) ->
                              ((let uu___191_10137 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
                                    (uu___191_10137.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___191_10137.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___192_10151 = x in
                           let uu____10152 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___192_10151.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___192_10151.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10152
                           } in
                         ((let uu___193_10158 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___193_10158.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___193_10158.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___194_10163 = x in
                           let uu____10164 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___194_10163.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___194_10163.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10164
                           } in
                         ((let uu___195_10170 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
                               (uu___195_10170.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___195_10170.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___196_10180 = x in
                           let uu____10181 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___196_10180.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___196_10180.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____10181
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___197_10188 = p in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
                               (uu___197_10188.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___197_10188.FStar_Syntax_Syntax.p)
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
                     | uu____10192 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____10195 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____10195 with
                                 | (p,wopt,e) ->
                                     let uu____10213 = norm_pat env1 p in
                                     (match uu____10213 with
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
                                                let uu____10237 =
                                                  norm_or_whnf env2 w in
                                                Some uu____10237 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____10242 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____10242) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____10252) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____10257 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10258;
                        FStar_Syntax_Syntax.fv_delta = uu____10259;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____10263;
                        FStar_Syntax_Syntax.fv_delta = uu____10264;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____10265);_}
                      -> true
                  | uu____10272 -> false in
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
                  let uu____10371 =
                    FStar_Syntax_Util.head_and_args scrutinee1 in
                  match uu____10371 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10403 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_wild uu____10405 ->
                           FStar_Util.Inl [scrutinee_orig]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10407 ->
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee1.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
                            | uu____10419 ->
                                let uu____10420 =
                                  let uu____10421 = is_cons head1 in
                                  Prims.op_Negation uu____10421 in
                                FStar_Util.Inr uu____10420)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10435 =
                             let uu____10436 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10436.FStar_Syntax_Syntax.n in
                           (match uu____10435 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10443 ->
                                let uu____10444 =
                                  let uu____10445 = is_cons head1 in
                                  Prims.op_Negation uu____10445 in
                                FStar_Util.Inr uu____10444))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10479)::rest_a,(p1,uu____10482)::rest_p) ->
                      let uu____10510 = matches_pat t1 p1 in
                      (match uu____10510 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____10524 -> FStar_Util.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
                      let uu____10595 = matches_pat scrutinee1 p1 in
                      (match uu____10595 with
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
                              (fun uu____10605  ->
                                 let uu____10606 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10607 =
                                   let uu____10608 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10608
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10606 uu____10607);
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
                                      let uu____10617 =
                                        let uu____10618 =
                                          let uu____10628 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10628, false) in
                                        Clos uu____10618 in
                                      uu____10617 :: env2) env1 s in
                             let uu____10651 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10651))) in
                let uu____10652 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10652
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___145_10666  ->
                match uu___145_10666 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____10669 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10673 -> d in
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
            let uu___198_10693 = config s e in
            {
              steps = (uu___198_10693.steps);
              tcenv = (uu___198_10693.tcenv);
              delta_level = (uu___198_10693.delta_level);
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
      fun t  -> let uu____10712 = config s e in norm_comp uu____10712 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____10719 = config [] env in norm_universe uu____10719 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
      let uu____10726 = config [] env in ghost_to_pure_aux uu____10726 [] c
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
        let uu____10738 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10738 in
      let uu____10739 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10739
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
            let uu___199_10741 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___199_10741.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___199_10741.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10742  ->
                    let uu____10743 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10743))
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
            ((let uu____10756 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10756);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____10765 = config [AllowUnboundUniverses] env in
          norm_comp uu____10765 [] c
        with
        | e ->
            ((let uu____10769 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10769);
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
                   let uu____10806 =
                     let uu____10807 =
                       let uu____10812 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10812) in
                     FStar_Syntax_Syntax.Tm_refine uu____10807 in
                   mk uu____10806 t01.FStar_Syntax_Syntax.pos
               | uu____10817 -> t2)
          | uu____10818 -> t2 in
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
        let uu____10840 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10840 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10856 ->
                 let uu____10860 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10860 with
                  | (actuals,uu____10871,uu____10872) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____10898 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10898 with
                         | (binders,args) ->
                             let uu____10908 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10911 =
                               let uu____10918 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_54  -> FStar_Util.Inl _0_54) in
                               FStar_All.pipe_right uu____10918
                                 (fun _0_55  -> Some _0_55) in
                             FStar_Syntax_Util.abs binders uu____10908
                               uu____10911)))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____10954 =
        let uu____10958 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10958, (t.FStar_Syntax_Syntax.n)) in
      match uu____10954 with
      | (Some sort,uu____10965) ->
          let uu____10967 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10967
      | (uu____10968,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10972 ->
          let uu____10976 = FStar_Syntax_Util.head_and_args t in
          (match uu____10976 with
           | (head1,args) ->
               let uu____11002 =
                 let uu____11003 = FStar_Syntax_Subst.compress head1 in
                 uu____11003.FStar_Syntax_Syntax.n in
               (match uu____11002 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____11006,thead) ->
                    let uu____11020 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____11020 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____11055 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_11059 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_11059.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_11059.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_11059.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_11059.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_11059.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_11059.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_11059.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_11059.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_11059.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_11059.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_11059.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_11059.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_11059.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_11059.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_11059.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_11059.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_11059.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_11059.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_11059.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_11059.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___204_11059.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_11059.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___204_11059.FStar_TypeChecker_Env.synth)
                                 }) t in
                            match uu____11055 with
                            | (uu____11060,ty,uu____11062) ->
                                eta_expand_with_type env t ty))
                | uu____11063 ->
                    let uu____11064 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_11068 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_11068.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_11068.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_11068.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_11068.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_11068.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_11068.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_11068.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_11068.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_11068.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_11068.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_11068.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_11068.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_11068.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_11068.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_11068.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_11068.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_11068.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_11068.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_11068.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_11068.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___205_11068.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_11068.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___205_11068.FStar_TypeChecker_Env.synth)
                         }) t in
                    (match uu____11064 with
                     | (uu____11069,ty,uu____11071) ->
                         eta_expand_with_type env t ty)))