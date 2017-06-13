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
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____68 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____72 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____76 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | AllowUnboundUniverses  -> true | uu____80 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  -> match projectee with | Reify  -> true | uu____84 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____88 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____92 -> false
type steps = step Prims.list
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  interpretation:
    FStar_Range.range ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option;}
type closure =
  | Clos of (closure Prims.list* FStar_Syntax_Syntax.term* (closure
  Prims.list* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo*
  Prims.bool)
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____175 -> false
let __proj__Clos__item___0:
  closure ->
    (closure Prims.list* FStar_Syntax_Syntax.term* (closure Prims.list*
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo* Prims.bool)
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____214 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____225 -> false
type env = closure Prims.list
let closure_to_string: closure -> Prims.string =
<<<<<<< HEAD
  fun uu___131_219  ->
    match uu___131_219 with
    | Clos (uu____220,t,uu____222,uu____223) ->
=======
  fun uu___130_229  ->
    match uu___130_229 with
    | Clos (uu____230,t,uu____232,uu____233) ->
>>>>>>> origin/master
        FStar_Syntax_Print.term_to_string t
    | Univ uu____244 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;}
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
    match projectee with | Arg _0 -> true | uu____371 -> false
let __proj__Arg__item___0:
  stack_elt -> (closure* FStar_Syntax_Syntax.aqual* FStar_Range.range) =
  fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____395 -> false
let __proj__UnivArgs__item___0:
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list* FStar_Range.range) =
  fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____419 -> false
let __proj__MemoLazy__item___0:
  stack_elt -> (env* FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____446 -> false
let __proj__Match__item___0: stack_elt -> (env* branches* FStar_Range.range)
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____475 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* env*
      (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either option* FStar_Range.range)
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____514 -> false
let __proj__App__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual* FStar_Range.range)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____537 -> false
let __proj__Meta__item___0:
  stack_elt -> (FStar_Syntax_Syntax.metadata* FStar_Range.range) =
  fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____559 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env* FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.letbinding*
      FStar_Range.range)
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Steps: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Steps _0 -> true | uu____588 -> false
let __proj__Steps__item___0:
  stack_elt ->
    (steps* primitive_step Prims.list* FStar_TypeChecker_Env.delta_level
      Prims.list)
  = fun projectee  -> match projectee with | Steps _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____615 -> false
let __proj__Debug__item___0: stack_elt -> FStar_Syntax_Syntax.term =
  fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let mk t r = FStar_Syntax_Syntax.mk t None r
let set_memo r t =
  let uu____663 = FStar_ST.read r in
  match uu____663 with
  | Some uu____668 -> failwith "Unexpected set_memo: thunk already evaluated"
  | None  -> FStar_ST.write r (Some t)
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____677 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____677 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
<<<<<<< HEAD
  fun uu___132_658  ->
    match uu___132_658 with
    | Arg (c,uu____660,uu____661) ->
        let uu____662 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____662
    | MemoLazy uu____663 -> "MemoLazy"
    | Abs (uu____667,bs,uu____669,uu____670,uu____671) ->
        let uu____678 =
=======
  fun uu___131_682  ->
    match uu___131_682 with
    | Arg (c,uu____684,uu____685) ->
        let uu____686 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____686
    | MemoLazy uu____687 -> "MemoLazy"
    | Abs (uu____691,bs,uu____693,uu____694,uu____695) ->
        let uu____702 =
>>>>>>> origin/master
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____702
    | UnivArgs uu____707 -> "UnivArgs"
    | Match uu____711 -> "Match"
    | App (t,uu____716,uu____717) ->
        let uu____718 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____718
    | Meta (m,uu____720) -> "Meta"
    | Let uu____721 -> "Let"
    | Steps (uu____726,uu____727,uu____728) -> "Steps"
    | Debug t ->
        let uu____734 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____734
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____740 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____740 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____754 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
<<<<<<< HEAD
      if uu____730 then f () else ()
let is_empty uu___133_739 =
  match uu___133_739 with | [] -> true | uu____741 -> false
=======
      if uu____754 then f () else ()
let is_empty uu___132_763 =
  match uu___132_763 with | [] -> true | uu____765 -> false
>>>>>>> origin/master
let lookup_bvar env x =
  try FStar_List.nth env x.FStar_Syntax_Syntax.index
  with
  | uu____783 ->
      let uu____784 =
        let uu____785 = FStar_Syntax_Print.db_to_string x in
        FStar_Util.format1 "Failed to find %s\n" uu____785 in
      failwith uu____784
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
          let uu____816 =
            FStar_List.fold_left
              (fun uu____825  ->
                 fun u1  ->
                   match uu____825 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____840 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____840 with
                        | (k_u,n1) ->
                            let uu____849 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____849
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____816 with
          | (uu____859,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____875 = FStar_List.nth env x in
                 match uu____875 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____878 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____882 ->
                   let uu____883 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____883
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_zero  -> [u2]
<<<<<<< HEAD
          | FStar_Syntax_Syntax.U_unif uu____863 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____868 -> [u2]
=======
          | FStar_Syntax_Syntax.U_unif uu____887 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____890 -> [u2]
>>>>>>> origin/master
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
<<<<<<< HEAD
                let uu____873 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____873 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____884 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____884 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____889 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____892 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____892 with
                                  | (uu____895,m) -> n1 <= m)) in
                        if uu____889 then rest1 else us1
                    | uu____899 -> us1)
               | uu____902 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____905 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____905 in
        let uu____907 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____907
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____909 = aux u in
           match uu____909 with
=======
                let uu____895 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____895 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____906 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____906 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____911 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____914 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____914 with
                                  | (uu____917,m) -> n1 <= m)) in
                        if uu____911 then rest1 else us1
                    | uu____921 -> us1)
               | uu____924 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____927 = aux u3 in
              FStar_List.map (fun _0_30  -> FStar_Syntax_Syntax.U_succ _0_30)
                uu____927 in
        let uu____929 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____929
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____931 = aux u in
           match uu____931 with
>>>>>>> origin/master
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
<<<<<<< HEAD
          (fun uu____1006  ->
             let uu____1007 = FStar_Syntax_Print.tag_of_term t in
             let uu____1008 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1007
               uu____1008);
=======
          (fun uu____1028  ->
             let uu____1029 = FStar_Syntax_Print.tag_of_term t in
             let uu____1030 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1029
               uu____1030);
>>>>>>> origin/master
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
<<<<<<< HEAD
         | uu____1009 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1012 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1033 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1034 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1035 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1036 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1048 =
                    let uu____1049 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1049 in
                  mk uu____1048 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1056 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1056
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1058 = lookup_bvar env x in
                  (match uu____1058 with
                   | Univ uu____1059 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1063) ->
=======
         | uu____1031 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1034 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1055 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1056 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1057 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1058 -> t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1068 =
                    let uu____1069 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1069 in
                  mk uu____1068 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t2,us) ->
                  let uu____1076 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t2 uu____1076
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1078 = lookup_bvar env x in
                  (match uu____1078 with
                   | Univ uu____1079 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,r,uu____1083) ->
>>>>>>> origin/master
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
<<<<<<< HEAD
                  let uu____1131 = closures_as_binders_delayed cfg env bs in
                  (match uu____1131 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1151 =
                         let uu____1152 =
                           let uu____1167 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1167) in
                         FStar_Syntax_Syntax.Tm_abs uu____1152 in
                       mk uu____1151 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1197 = closures_as_binders_delayed cfg env bs in
                  (match uu____1197 with
=======
                  let uu____1151 = closures_as_binders_delayed cfg env bs in
                  (match uu____1151 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____1171 =
                         let uu____1172 =
                           let uu____1187 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____1187) in
                         FStar_Syntax_Syntax.Tm_abs uu____1172 in
                       mk uu____1171 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____1217 = closures_as_binders_delayed cfg env bs in
                  (match uu____1217 with
>>>>>>> origin/master
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
<<<<<<< HEAD
                  let uu____1228 =
                    let uu____1235 =
                      let uu____1239 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1239] in
                    closures_as_binders_delayed cfg env uu____1235 in
                  (match uu____1228 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1253 =
                         let uu____1254 =
                           let uu____1259 =
                             let uu____1260 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1260
                               FStar_Pervasives.fst in
                           (uu____1259, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1254 in
                       mk uu____1253 t1.FStar_Syntax_Syntax.pos)
=======
                  let uu____1248 =
                    let uu____1255 =
                      let uu____1259 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____1259] in
                    closures_as_binders_delayed cfg env uu____1255 in
                  (match uu____1248 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____1273 =
                         let uu____1274 =
                           let uu____1279 =
                             let uu____1280 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____1280
                               FStar_Pervasives.fst in
                           (uu____1279, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____1274 in
                       mk uu____1273 t1.FStar_Syntax_Syntax.pos)
>>>>>>> origin/master
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
<<<<<<< HEAD
                        let uu____1328 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1328
                    | FStar_Util.Inr c ->
                        let uu____1342 = close_comp cfg env c in
                        FStar_Util.Inr uu____1342 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1357 =
                    let uu____1358 =
                      let uu____1376 = closure_as_term_delayed cfg env t11 in
                      (uu____1376, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1358 in
                  mk uu____1357 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1414 =
                    let uu____1415 =
                      let uu____1420 = closure_as_term_delayed cfg env t' in
                      let uu____1423 =
                        let uu____1424 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1424 in
                      (uu____1420, uu____1423) in
                    FStar_Syntax_Syntax.Tm_meta uu____1415 in
                  mk uu____1414 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1466 =
                    let uu____1467 =
                      let uu____1472 = closure_as_term_delayed cfg env t' in
                      let uu____1475 =
                        let uu____1476 =
                          let uu____1481 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1481) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1476 in
                      (uu____1472, uu____1475) in
                    FStar_Syntax_Syntax.Tm_meta uu____1467 in
                  mk uu____1466 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1500 =
                    let uu____1501 =
                      let uu____1506 = closure_as_term_delayed cfg env t' in
                      let uu____1509 =
                        let uu____1510 =
                          let uu____1516 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1516) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1510 in
                      (uu____1506, uu____1509) in
                    FStar_Syntax_Syntax.Tm_meta uu____1501 in
                  mk uu____1500 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1529 =
                    let uu____1530 =
                      let uu____1535 = closure_as_term_delayed cfg env t' in
                      (uu____1535, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1530 in
                  mk uu____1529 t1.FStar_Syntax_Syntax.pos
=======
                        let uu____1348 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____1348
                    | FStar_Util.Inr c ->
                        let uu____1362 = close_comp cfg env c in
                        FStar_Util.Inr uu____1362 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____1377 =
                    let uu____1378 =
                      let uu____1396 = closure_as_term_delayed cfg env t11 in
                      (uu____1396, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____1378 in
                  mk uu____1377 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____1434 =
                    let uu____1435 =
                      let uu____1440 = closure_as_term_delayed cfg env t' in
                      let uu____1443 =
                        let uu____1444 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____1444 in
                      (uu____1440, uu____1443) in
                    FStar_Syntax_Syntax.Tm_meta uu____1435 in
                  mk uu____1434 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____1486 =
                    let uu____1487 =
                      let uu____1492 = closure_as_term_delayed cfg env t' in
                      let uu____1495 =
                        let uu____1496 =
                          let uu____1501 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____1501) in
                        FStar_Syntax_Syntax.Meta_monadic uu____1496 in
                      (uu____1492, uu____1495) in
                    FStar_Syntax_Syntax.Tm_meta uu____1487 in
                  mk uu____1486 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____1520 =
                    let uu____1521 =
                      let uu____1526 = closure_as_term_delayed cfg env t' in
                      let uu____1529 =
                        let uu____1530 =
                          let uu____1536 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____1536) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____1530 in
                      (uu____1526, uu____1529) in
                    FStar_Syntax_Syntax.Tm_meta uu____1521 in
                  mk uu____1520 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____1549 =
                    let uu____1550 =
                      let uu____1555 = closure_as_term_delayed cfg env t' in
                      (uu____1555, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____1550 in
                  mk uu____1549 t1.FStar_Syntax_Syntax.pos
>>>>>>> origin/master
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
<<<<<<< HEAD
                      (fun env1  -> fun uu____1556  -> Dummy :: env1) env
=======
                      (fun env1  -> fun uu____1576  -> Dummy :: env1) env
>>>>>>> origin/master
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let body1 =
                    match lb.FStar_Syntax_Syntax.lbname with
<<<<<<< HEAD
                    | FStar_Util.Inr uu____1567 -> body
                    | FStar_Util.Inl uu____1568 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___147_1570 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___147_1570.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___147_1570.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___147_1570.FStar_Syntax_Syntax.lbeff);
=======
                    | FStar_Util.Inr uu____1587 -> body
                    | FStar_Util.Inl uu____1588 ->
                        closure_as_term cfg (Dummy :: env0) body in
                  let lb1 =
                    let uu___145_1590 = lb in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___145_1590.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___145_1590.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = typ;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___145_1590.FStar_Syntax_Syntax.lbeff);
>>>>>>> origin/master
                      FStar_Syntax_Syntax.lbdef = def
                    } in
                  mk (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                    t1.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
              | FStar_Syntax_Syntax.Tm_let ((uu____1577,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1601  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1606 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1606
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1610  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___148_1613 = lb in
                    let uu____1614 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1617 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___148_1613.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___148_1613.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1614;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___148_1613.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1617
=======
              | FStar_Syntax_Syntax.Tm_let ((uu____1597,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____1621  -> fun env2  -> Dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____1626 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____1626
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____1630  -> fun env2  -> Dummy :: env2) lbs
                          env_univs in
                    let uu___146_1633 = lb in
                    let uu____1634 =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____1637 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname =
                        (uu___146_1633.FStar_Syntax_Syntax.lbname);
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___146_1633.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = uu____1634;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___146_1633.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____1637
>>>>>>> origin/master
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
<<<<<<< HEAD
                        (fun uu____1628  -> fun env1  -> Dummy :: env1) lbs1
=======
                        (fun uu____1648  -> fun env1  -> Dummy :: env1) lbs1
>>>>>>> origin/master
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
<<<<<<< HEAD
                  let norm_one_branch env1 uu____1683 =
                    match uu____1683 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1729 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1745 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1779  ->
                                        fun uu____1780  ->
                                          match (uu____1779, uu____1780) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1845 =
                                                norm_pat env3 p1 in
                                              (match uu____1845 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1745 with
                               | (pats1,env3) ->
                                   ((let uu___149_1911 = p in
=======
                  let norm_one_branch env1 uu____1703 =
                    match uu____1703 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____1749 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____1765 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____1799  ->
                                        fun uu____1800  ->
                                          match (uu____1799, uu____1800) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____1865 =
                                                norm_pat env3 p1 in
                                              (match uu____1865 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____1765 with
                               | (pats1,env3) ->
                                   ((let uu___147_1931 = p in
>>>>>>> origin/master
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                                         (uu___149_1911.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___149_1911.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___150_1925 = x in
                                let uu____1926 =
=======
                                         (uu___147_1931.FStar_Syntax_Syntax.ty);
                                       FStar_Syntax_Syntax.p =
                                         (uu___147_1931.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___148_1945 = x in
                                let uu____1946 =
>>>>>>> origin/master
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                    (uu___150_1925.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___150_1925.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1926
                                } in
                              ((let uu___151_1932 = p in
=======
                                    (uu___148_1945.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___148_1945.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1946
                                } in
                              ((let uu___149_1952 = p in
>>>>>>> origin/master
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                                    (uu___151_1932.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___151_1932.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___152_1937 = x in
                                let uu____1938 =
=======
                                    (uu___149_1952.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___149_1952.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___150_1957 = x in
                                let uu____1958 =
>>>>>>> origin/master
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                    (uu___152_1937.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1937.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1938
                                } in
                              ((let uu___153_1944 = p in
=======
                                    (uu___150_1957.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___150_1957.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1958
                                } in
                              ((let uu___151_1964 = p in
>>>>>>> origin/master
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                                    (uu___153_1944.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1944.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___154_1954 = x in
                                let uu____1955 =
=======
                                    (uu___151_1964.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___151_1964.FStar_Syntax_Syntax.p)
                                }), (Dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___152_1974 = x in
                                let uu____1975 =
>>>>>>> origin/master
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                    (uu___154_1954.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___154_1954.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1955
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___155_1962 = p in
=======
                                    (uu___152_1974.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___152_1974.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____1975
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___153_1982 = p in
>>>>>>> origin/master
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                                    (uu___155_1962.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___155_1962.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1965 = norm_pat env1 pat in
                        (match uu____1965 with
=======
                                    (uu___153_1982.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___153_1982.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____1985 = norm_pat env1 pat in
                        (match uu____1985 with
>>>>>>> origin/master
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | None  -> None
                               | Some w ->
<<<<<<< HEAD
                                   let uu____1989 =
                                     closure_as_term cfg env2 w in
                                   Some uu____1989 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____1994 =
                    let uu____1995 =
                      let uu____2011 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2011) in
                    FStar_Syntax_Syntax.Tm_match uu____1995 in
                  mk uu____1994 t1.FStar_Syntax_Syntax.pos))
=======
                                   let uu____2009 =
                                     closure_as_term cfg env2 w in
                                   Some uu____2009 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____2014 =
                    let uu____2015 =
                      let uu____2031 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____2031) in
                    FStar_Syntax_Syntax.Tm_match uu____2015 in
                  mk uu____2014 t1.FStar_Syntax_Syntax.pos))
>>>>>>> origin/master
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
<<<<<<< HEAD
        | uu____2064 -> closure_as_term cfg env t
=======
        | uu____2084 -> closure_as_term cfg env t
>>>>>>> origin/master
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
<<<<<<< HEAD
        | uu____2080 ->
            FStar_List.map
              (fun uu____2090  ->
                 match uu____2090 with
                 | (x,imp) ->
                     let uu____2105 = closure_as_term_delayed cfg env x in
                     (uu____2105, imp)) args
=======
        | uu____2100 ->
            FStar_List.map
              (fun uu____2110  ->
                 match uu____2110 with
                 | (x,imp) ->
                     let uu____2125 = closure_as_term_delayed cfg env x in
                     (uu____2125, imp)) args
>>>>>>> origin/master
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
<<<<<<< HEAD
        let uu____2117 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2141  ->
                  fun uu____2142  ->
                    match (uu____2141, uu____2142) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___156_2186 = b in
                          let uu____2187 =
=======
        let uu____2137 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____2161  ->
                  fun uu____2162  ->
                    match (uu____2161, uu____2162) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___154_2206 = b in
                          let uu____2207 =
>>>>>>> origin/master
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                              (uu___156_2186.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___156_2186.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2187
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2117 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
=======
                              (uu___154_2206.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___154_2206.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____2207
                          } in
                        let env2 = Dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____2137 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
>>>>>>> origin/master
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
<<<<<<< HEAD
        | uu____2234 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2246 = closure_as_term_delayed cfg env t in
                 let uu____2247 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2246 uu____2247
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2257 = closure_as_term_delayed cfg env t in
                 let uu____2258 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2257 uu____2258
=======
        | uu____2254 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____2266 = closure_as_term_delayed cfg env t in
                 let uu____2267 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____2266 uu____2267
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____2277 = closure_as_term_delayed cfg env t in
                 let uu____2278 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____2277 uu____2278
>>>>>>> origin/master
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
<<<<<<< HEAD
                        (fun uu___134_2274  ->
                           match uu___134_2274 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2278 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2278
                           | f -> f)) in
                 let uu____2282 =
                   let uu___157_2283 = c1 in
                   let uu____2284 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2284;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___157_2283.FStar_Syntax_Syntax.effect_name);
=======
                        (fun uu___133_2294  ->
                           match uu___133_2294 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____2298 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____2298
                           | f -> f)) in
                 let uu____2302 =
                   let uu___155_2303 = c1 in
                   let uu____2304 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____2304;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___155_2303.FStar_Syntax_Syntax.effect_name);
>>>>>>> origin/master
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
<<<<<<< HEAD
                 FStar_Syntax_Syntax.mk_Comp uu____2282)
=======
                 FStar_Syntax_Syntax.mk_Comp uu____2302)
>>>>>>> origin/master
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.cflags Prims.list =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_List.filter
<<<<<<< HEAD
         (fun uu___135_2288  ->
            match uu___135_2288 with
            | FStar_Syntax_Syntax.DECREASES uu____2289 -> false
            | uu____2292 -> true))
=======
         (fun uu___134_2308  ->
            match uu___134_2308 with
            | FStar_Syntax_Syntax.DECREASES uu____2309 -> false
            | uu____2312 -> true))
>>>>>>> origin/master
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
<<<<<<< HEAD
            let uu____2320 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2320
=======
            let uu____2340 = FStar_Syntax_Util.is_total_lcomp lc in
            if uu____2340
>>>>>>> origin/master
            then
              Some
                (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, flags))
            else
<<<<<<< HEAD
              (let uu____2337 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2337
=======
              (let uu____2357 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
               if uu____2357
>>>>>>> origin/master
               then
                 Some
                   (FStar_Util.Inr
                      (FStar_Syntax_Const.effect_GTot_lid, flags))
               else
                 Some
                   (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags)))
<<<<<<< HEAD
        | uu____2363 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2387 =
      let uu____2388 =
        let uu____2394 = FStar_Util.string_of_int i in (uu____2394, None) in
      FStar_Const.Const_int uu____2388 in
    const_as_tm uu____2387 p in
=======
        | uu____2383 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let const_as_tm c p = mk (FStar_Syntax_Syntax.Tm_constant c) p in
  let int_as_const p i =
    let uu____2407 =
      let uu____2408 =
        let uu____2414 = FStar_Util.string_of_int i in (uu____2414, None) in
      FStar_Const.Const_int uu____2408 in
    const_as_tm uu____2407 p in
>>>>>>> origin/master
  let bool_as_const p b = const_as_tm (FStar_Const.Const_bool b) p in
  let string_as_const p b =
    const_as_tm
      (FStar_Const.Const_string ((FStar_Util.bytes_of_string b), p)) p in
<<<<<<< HEAD
  let arg_as_int uu____2421 =
    match uu____2421 with
    | (a,uu____2426) ->
        let uu____2428 =
          let uu____2429 = FStar_Syntax_Subst.compress a in
          uu____2429.FStar_Syntax_Syntax.n in
        (match uu____2428 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2439 = FStar_Util.int_of_string i in Some uu____2439
         | uu____2440 -> None) in
  let arg_as_bounded_int uu____2449 =
    match uu____2449 with
    | (a,uu____2456) ->
        let uu____2460 =
          let uu____2461 = FStar_Syntax_Subst.compress a in
          uu____2461.FStar_Syntax_Syntax.n in
        (match uu____2460 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2468;
                FStar_Syntax_Syntax.pos = uu____2469;
                FStar_Syntax_Syntax.vars = uu____2470;_},({
=======
  let arg_as_int uu____2441 =
    match uu____2441 with
    | (a,uu____2446) ->
        let uu____2448 =
          let uu____2449 = FStar_Syntax_Subst.compress a in
          uu____2449.FStar_Syntax_Syntax.n in
        (match uu____2448 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i,None ))
             ->
             let uu____2459 = FStar_Util.int_of_string i in Some uu____2459
         | uu____2460 -> None) in
  let arg_as_bounded_int uu____2469 =
    match uu____2469 with
    | (a,uu____2476) ->
        let uu____2480 =
          let uu____2481 = FStar_Syntax_Subst.compress a in
          uu____2481.FStar_Syntax_Syntax.n in
        (match uu____2480 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.tk = uu____2488;
                FStar_Syntax_Syntax.pos = uu____2489;
                FStar_Syntax_Syntax.vars = uu____2490;_},({
>>>>>>> origin/master
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,None ));
                                                            FStar_Syntax_Syntax.tk
<<<<<<< HEAD
                                                              = uu____2472;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2473;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2474;_},uu____2475)::[])
=======
                                                              = uu____2492;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____2493;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____2494;_},uu____2495)::[])
>>>>>>> origin/master
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
<<<<<<< HEAD
             let uu____2506 =
               let uu____2509 = FStar_Util.int_of_string i in
               (fv1, uu____2509) in
             Some uu____2506
         | uu____2512 -> None) in
  let arg_as_bool uu____2521 =
    match uu____2521 with
    | (a,uu____2526) ->
        let uu____2528 =
          let uu____2529 = FStar_Syntax_Subst.compress a in
          uu____2529.FStar_Syntax_Syntax.n in
        (match uu____2528 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2534 -> None) in
  let arg_as_char uu____2541 =
    match uu____2541 with
    | (a,uu____2546) ->
        let uu____2548 =
          let uu____2549 = FStar_Syntax_Subst.compress a in
          uu____2549.FStar_Syntax_Syntax.n in
        (match uu____2548 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2554 -> None) in
  let arg_as_string uu____2561 =
    match uu____2561 with
    | (a,uu____2566) ->
        let uu____2568 =
          let uu____2569 = FStar_Syntax_Subst.compress a in
          uu____2569.FStar_Syntax_Syntax.n in
        (match uu____2568 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2574)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2577 -> None) in
  let arg_as_list f uu____2598 =
    match uu____2598 with
    | (a,uu____2607) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2626 -> None
          | (Some x)::xs ->
              let uu____2636 = sequence xs in
              (match uu____2636 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2647 = FStar_Syntax_Util.list_elements a in
        (match uu____2647 with
         | None  -> None
         | Some elts ->
             let uu____2657 =
               FStar_List.map
                 (fun x  ->
                    let uu____2662 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2662) elts in
             sequence uu____2657) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2692 = f a in Some uu____2692
    | uu____2693 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2732 = f a0 a1 in Some uu____2732
    | uu____2733 -> None in
  let unary_op as_a f r args =
    let uu____2777 = FStar_List.map as_a args in lift_unary (f r) uu____2777 in
  let binary_op as_a f r args =
    let uu____2827 = FStar_List.map as_a args in lift_binary (f r) uu____2827 in
  let as_primitive_step uu____2844 =
    match uu____2844 with
=======
             let uu____2526 =
               let uu____2529 = FStar_Util.int_of_string i in
               (fv1, uu____2529) in
             Some uu____2526
         | uu____2532 -> None) in
  let arg_as_bool uu____2541 =
    match uu____2541 with
    | (a,uu____2546) ->
        let uu____2548 =
          let uu____2549 = FStar_Syntax_Subst.compress a in
          uu____2549.FStar_Syntax_Syntax.n in
        (match uu____2548 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
             Some b
         | uu____2554 -> None) in
  let arg_as_char uu____2561 =
    match uu____2561 with
    | (a,uu____2566) ->
        let uu____2568 =
          let uu____2569 = FStar_Syntax_Subst.compress a in
          uu____2569.FStar_Syntax_Syntax.n in
        (match uu____2568 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
             Some c
         | uu____2574 -> None) in
  let arg_as_string uu____2581 =
    match uu____2581 with
    | (a,uu____2586) ->
        let uu____2588 =
          let uu____2589 = FStar_Syntax_Subst.compress a in
          uu____2589.FStar_Syntax_Syntax.n in
        (match uu____2588 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (bytes,uu____2594)) -> Some (FStar_Util.string_of_bytes bytes)
         | uu____2597 -> None) in
  let arg_as_list f uu____2618 =
    match uu____2618 with
    | (a,uu____2627) ->
        let rec sequence l =
          match l with
          | [] -> Some []
          | (None )::uu____2646 -> None
          | (Some x)::xs ->
              let uu____2656 = sequence xs in
              (match uu____2656 with
               | None  -> None
               | Some xs' -> Some (x :: xs')) in
        let uu____2667 = FStar_Syntax_Util.list_elements a in
        (match uu____2667 with
         | None  -> None
         | Some elts ->
             let uu____2677 =
               FStar_List.map
                 (fun x  ->
                    let uu____2682 = FStar_Syntax_Syntax.as_arg x in
                    f uu____2682) elts in
             sequence uu____2677) in
  let lift_unary f aopts =
    match aopts with
    | (Some a)::[] -> let uu____2712 = f a in Some uu____2712
    | uu____2713 -> None in
  let lift_binary f aopts =
    match aopts with
    | (Some a0)::(Some a1)::[] -> let uu____2752 = f a0 a1 in Some uu____2752
    | uu____2753 -> None in
  let unary_op as_a f r args =
    let uu____2797 = FStar_List.map as_a args in lift_unary (f r) uu____2797 in
  let binary_op as_a f r args =
    let uu____2847 = FStar_List.map as_a args in lift_binary (f r) uu____2847 in
  let as_primitive_step uu____2864 =
    match uu____2864 with
>>>>>>> origin/master
    | (l,arity,f) ->
        { name = l; arity; strong_reduction_ok = true; interpretation = f } in
  let unary_int_op f =
    unary_op arg_as_int
<<<<<<< HEAD
      (fun r  -> fun x  -> let uu____2882 = f x in int_as_const r uu____2882) in
=======
      (fun r  -> fun x  -> let uu____2902 = f x in int_as_const r uu____2902) in
>>>>>>> origin/master
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
<<<<<<< HEAD
           fun y  -> let uu____2905 = f x y in int_as_const r uu____2905) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2922 = f x in bool_as_const r uu____2922) in
=======
           fun y  -> let uu____2925 = f x y in int_as_const r uu____2925) in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  -> fun x  -> let uu____2942 = f x in bool_as_const r uu____2942) in
>>>>>>> origin/master
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
<<<<<<< HEAD
           fun y  -> let uu____2945 = f x y in bool_as_const r uu____2945) in
=======
           fun y  -> let uu____2965 = f x y in bool_as_const r uu____2965) in
>>>>>>> origin/master
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
<<<<<<< HEAD
           fun y  -> let uu____2968 = f x y in string_as_const r uu____2968) in
  let list_of_string' rng s =
    let name l =
      let uu____2982 =
        let uu____2983 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____2983 in
      mk uu____2982 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____2993 =
      let uu____2995 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____2995 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____2993 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3017 = FStar_Util.string_of_int i in
    string_as_const rng uu____3017 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3033 = FStar_Util.string_of_int i in
    string_as_const rng uu____3033 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3052 =
      let uu____3062 =
        let uu____3072 =
          let uu____3082 =
            let uu____3092 =
              let uu____3102 =
                let uu____3112 =
                  let uu____3122 =
                    let uu____3132 =
                      let uu____3142 =
                        let uu____3152 =
                          let uu____3162 =
                            let uu____3172 =
                              let uu____3182 =
                                let uu____3192 =
                                  let uu____3202 =
                                    let uu____3212 =
                                      let uu____3221 =
=======
           fun y  -> let uu____2988 = f x y in string_as_const r uu____2988) in
  let list_of_string' rng s =
    let name l =
      let uu____3002 =
        let uu____3003 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            None in
        FStar_Syntax_Syntax.Tm_fvar uu____3003 in
      mk uu____3002 rng in
    let char_t = name FStar_Syntax_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____3013 =
      let uu____3015 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____3015 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3013 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Const.exp_string s in
  let string_of_int1 rng i =
    let uu____3037 = FStar_Util.string_of_int i in
    string_as_const rng uu____3037 in
  let string_of_bool1 rng b =
    string_as_const rng (if b then "true" else "false") in
  let string_of_int2 rng i =
    let uu____3053 = FStar_Util.string_of_int i in
    string_as_const rng uu____3053 in
  let string_of_bool2 rng b =
    string_as_const rng (if b then "true" else "false") in
  let basic_ops =
    let uu____3072 =
      let uu____3082 =
        let uu____3092 =
          let uu____3102 =
            let uu____3112 =
              let uu____3122 =
                let uu____3132 =
                  let uu____3142 =
                    let uu____3152 =
                      let uu____3162 =
                        let uu____3172 =
                          let uu____3182 =
                            let uu____3192 =
                              let uu____3202 =
                                let uu____3212 =
                                  let uu____3222 =
                                    let uu____3232 =
                                      let uu____3241 =
>>>>>>> origin/master
                                        FStar_Syntax_Const.p2l
                                          ["FStar";
                                          "String";
                                          "list_of_string"] in
<<<<<<< HEAD
                                      (uu____3221, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3227 =
                                      let uu____3237 =
                                        let uu____3246 =
=======
                                      (uu____3241, (Prims.parse_int "1"),
                                        (unary_op arg_as_string
                                           list_of_string')) in
                                    let uu____3247 =
                                      let uu____3257 =
                                        let uu____3266 =
>>>>>>> origin/master
                                          FStar_Syntax_Const.p2l
                                            ["FStar";
                                            "String";
                                            "string_of_list"] in
<<<<<<< HEAD
                                        (uu____3246, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3237] in
                                    uu____3212 :: uu____3227 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3202 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3192 in
=======
                                        (uu____3266, (Prims.parse_int "1"),
                                          (unary_op (arg_as_list arg_as_char)
                                             string_of_list')) in
                                      [uu____3257] in
                                    uu____3232 :: uu____3247 in
                                  (FStar_Syntax_Const.string_of_bool_lid,
                                    (Prims.parse_int "1"),
                                    (unary_op arg_as_bool string_of_bool2))
                                    :: uu____3222 in
                                (FStar_Syntax_Const.string_of_int_lid,
                                  (Prims.parse_int "1"),
                                  (unary_op arg_as_int string_of_int2)) ::
                                  uu____3212 in
>>>>>>> origin/master
                              (FStar_Syntax_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
<<<<<<< HEAD
                                :: uu____3182 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3172 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3162 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3152 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3142 in
=======
                                :: uu____3202 in
                            (FStar_Syntax_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____3192 in
                          (FStar_Syntax_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____3182 in
                        (FStar_Syntax_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____3172 in
                      (FStar_Syntax_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op (fun x  -> fun y  -> x mod y))) ::
                        uu____3162 in
>>>>>>> origin/master
                    (FStar_Syntax_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  -> fun y  -> bool_as_const r (x >= y))))
<<<<<<< HEAD
                      :: uu____3132 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3122 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3112 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3102 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3092 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3082 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3072 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3062 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3052 in
=======
                      :: uu____3152 in
                  (FStar_Syntax_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  -> fun x  -> fun y  -> bool_as_const r (x > y))))
                    :: uu____3142 in
                (FStar_Syntax_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  -> fun x  -> fun y  -> bool_as_const r (x <= y))))
                  :: uu____3132 in
              (FStar_Syntax_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  -> fun x  -> fun y  -> bool_as_const r (x < y))))
                :: uu____3122 in
            (FStar_Syntax_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op (fun x  -> fun y  -> x / y))) :: uu____3112 in
          (FStar_Syntax_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op (fun x  -> fun y  -> x * y))) :: uu____3102 in
        (FStar_Syntax_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> x - y))) :: uu____3092 in
      (FStar_Syntax_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> x + y))) :: uu____3082 in
    (FStar_Syntax_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> - x))) :: uu____3072 in
>>>>>>> origin/master
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
<<<<<<< HEAD
      let uu____3541 =
        let uu____3542 =
          let uu____3543 = FStar_Syntax_Syntax.as_arg c in [uu____3543] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3542 in
      uu____3541 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3567 =
              let uu____3576 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3576, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3585  ->
                        fun uu____3586  ->
                          match (uu____3585, uu____3586) with
                          | ((int_to_t1,x),(uu____3597,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3603 =
              let uu____3613 =
                let uu____3622 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3622, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3631  ->
                          fun uu____3632  ->
                            match (uu____3631, uu____3632) with
                            | ((int_to_t1,x),(uu____3643,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3649 =
                let uu____3659 =
                  let uu____3668 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3668, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3677  ->
                            fun uu____3678  ->
                              match (uu____3677, uu____3678) with
                              | ((int_to_t1,x),(uu____3689,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3659] in
              uu____3613 :: uu____3649 in
            uu____3567 :: uu____3603)) in
=======
      let uu____3561 =
        let uu____3562 =
          let uu____3563 = FStar_Syntax_Syntax.as_arg c in [uu____3563] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____3562 in
      uu____3561 None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____3587 =
              let uu____3596 = FStar_Syntax_Const.p2l ["FStar"; m; "add"] in
              (uu____3596, (Prims.parse_int "2"),
                (binary_op arg_as_bounded_int
                   (fun r  ->
                      fun uu____3605  ->
                        fun uu____3606  ->
                          match (uu____3605, uu____3606) with
                          | ((int_to_t1,x),(uu____3617,y)) ->
                              int_as_bounded r int_to_t1 (x + y)))) in
            let uu____3623 =
              let uu____3633 =
                let uu____3642 = FStar_Syntax_Const.p2l ["FStar"; m; "sub"] in
                (uu____3642, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____3651  ->
                          fun uu____3652  ->
                            match (uu____3651, uu____3652) with
                            | ((int_to_t1,x),(uu____3663,y)) ->
                                int_as_bounded r int_to_t1 (x - y)))) in
              let uu____3669 =
                let uu____3679 =
                  let uu____3688 = FStar_Syntax_Const.p2l ["FStar"; m; "mul"] in
                  (uu____3688, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____3697  ->
                            fun uu____3698  ->
                              match (uu____3697, uu____3698) with
                              | ((int_to_t1,x),(uu____3709,y)) ->
                                  int_as_bounded r int_to_t1 (x * y)))) in
                [uu____3679] in
              uu____3633 :: uu____3669 in
            uu____3587 :: uu____3623)) in
>>>>>>> origin/master
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_bool rng args =
    match args with
<<<<<<< HEAD
    | (_typ,uu____3755)::(a1,uu____3757)::(a2,uu____3759)::[] ->
        let uu____3788 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3788 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3790 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3790
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3795 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3795
         | uu____3800 -> None)
    | uu____3801 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3814)::(a1,uu____3816)::(a2,uu____3818)::[] ->
        let uu____3847 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3847 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___158_3851 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3851.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3851.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3851.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___159_3858 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___159_3858.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___159_3858.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3858.FStar_Syntax_Syntax.vars)
                })
         | uu____3863 -> None)
    | (_typ,uu____3865)::uu____3866::(a1,uu____3868)::(a2,uu____3870)::[] ->
        let uu____3907 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3907 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___158_3911 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___158_3911.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___158_3911.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___158_3911.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___159_3918 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___159_3918.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___159_3918.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3918.FStar_Syntax_Syntax.vars)
                })
         | uu____3923 -> None)
    | uu____3924 -> failwith "Unexpected number of arguments" in
=======
    | (_typ,uu____3775)::(a1,uu____3777)::(a2,uu____3779)::[] ->
        let uu____3808 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3808 with
         | FStar_Syntax_Util.Equal  ->
             let uu____3810 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool true)) rng in
             Some uu____3810
         | FStar_Syntax_Util.NotEqual  ->
             let uu____3815 =
               mk
                 (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_bool false)) rng in
             Some uu____3815
         | uu____3820 -> None)
    | uu____3821 -> failwith "Unexpected number of arguments" in
  let interp_prop r args =
    match args with
    | (_typ,uu____3834)::(a1,uu____3836)::(a2,uu____3838)::[] ->
        let uu____3867 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3867 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___156_3871 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_3871.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_3871.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_3871.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___157_3878 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3878.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3878.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3878.FStar_Syntax_Syntax.vars)
                })
         | uu____3883 -> None)
    | (_typ,uu____3885)::uu____3886::(a1,uu____3888)::(a2,uu____3890)::[] ->
        let uu____3927 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____3927 with
         | FStar_Syntax_Util.Equal  ->
             Some
               (let uu___156_3931 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___156_3931.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___156_3931.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___156_3931.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             Some
               (let uu___157_3938 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___157_3938.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___157_3938.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___157_3938.FStar_Syntax_Syntax.vars)
                })
         | uu____3943 -> None)
    | uu____3944 -> failwith "Unexpected number of arguments" in
>>>>>>> origin/master
  let decidable_equality =
    {
      name = FStar_Syntax_Const.op_Eq;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      interpretation = interp_bool
    } in
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
  [decidable_equality; propositional_equality; hetero_propositional_equality]
let reduce_primops:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
<<<<<<< HEAD
      let uu____3935 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3935
      then tm
      else
        (let uu____3937 = FStar_Syntax_Util.head_and_args tm in
         match uu____3937 with
         | (head1,args) ->
             let uu____3963 =
               let uu____3964 = FStar_Syntax_Util.un_uinst head1 in
               uu____3964.FStar_Syntax_Syntax.n in
             (match uu____3963 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3968 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3968 with
=======
      let uu____3955 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Primops cfg.steps) in
      if uu____3955
      then tm
      else
        (let uu____3957 = FStar_Syntax_Util.head_and_args tm in
         match uu____3957 with
         | (head1,args) ->
             let uu____3983 =
               let uu____3984 = FStar_Syntax_Util.un_uinst head1 in
               uu____3984.FStar_Syntax_Syntax.n in
             (match uu____3983 with
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let uu____3988 =
                    FStar_List.tryFind
                      (fun ps  -> FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                      cfg.primitive_steps in
                  (match uu____3988 with
>>>>>>> origin/master
                   | None  -> tm
                   | Some prim_step ->
                       if (FStar_List.length args) < prim_step.arity
                       then tm
                       else
<<<<<<< HEAD
                         (let uu____3980 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____3980 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____3983 -> tm))
=======
                         (let uu____4000 =
                            prim_step.interpretation
                              head1.FStar_Syntax_Syntax.pos args in
                          match uu____4000 with
                          | None  -> tm
                          | Some reduced -> reduced))
              | uu____4003 -> tm))
>>>>>>> origin/master
let reduce_equality:
  cfg -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun tm  ->
      reduce_primops
<<<<<<< HEAD
        (let uu___160_3990 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___160_3990.tcenv);
           delta_level = (uu___160_3990.delta_level);
=======
        (let uu___158_4010 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___158_4010.tcenv);
           delta_level = (uu___158_4010.delta_level);
>>>>>>> origin/master
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
<<<<<<< HEAD
        let uu___161_4012 = t in
        {
          FStar_Syntax_Syntax.n = (uu___161_4012.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___161_4012.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___161_4012.FStar_Syntax_Syntax.vars)
=======
        let uu___159_4032 = t in
        {
          FStar_Syntax_Syntax.n = (uu___159_4032.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___159_4032.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___159_4032.FStar_Syntax_Syntax.vars)
>>>>>>> origin/master
        } in
      let simp_t t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid ->
            Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid ->
            Some false
<<<<<<< HEAD
        | uu____4031 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4058 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4058
=======
        | uu____4051 -> None in
      let simplify arg = ((simp_t (fst arg)), arg) in
      let uu____4078 =
        FStar_All.pipe_left Prims.op_Negation
          (FStar_List.contains Simplify steps) in
      if uu____4078
>>>>>>> origin/master
      then reduce_primops cfg tm
      else
        (match tm.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
<<<<<<< HEAD
                     FStar_Syntax_Syntax.tk = uu____4061;
                     FStar_Syntax_Syntax.pos = uu____4062;
                     FStar_Syntax_Syntax.vars = uu____4063;_},uu____4064);
                FStar_Syntax_Syntax.tk = uu____4065;
                FStar_Syntax_Syntax.pos = uu____4066;
                FStar_Syntax_Syntax.vars = uu____4067;_},args)
             ->
             let uu____4087 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4087
             then
               let uu____4088 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4088 with
                | (Some (true ),uu____4121)::(uu____4122,(arg,uu____4124))::[]
                    -> arg
                | (uu____4165,(arg,uu____4167))::(Some (true ),uu____4168)::[]
                    -> arg
                | (Some (false ),uu____4209)::uu____4210::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4248::(Some (false ),uu____4249)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4287 -> tm)
             else
               (let uu____4297 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4297
                then
                  let uu____4298 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4298 with
                  | (Some (true ),uu____4331)::uu____4332::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4370::(Some (true ),uu____4371)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4409)::(uu____4410,(arg,uu____4412))::[]
                      -> arg
                  | (uu____4453,(arg,uu____4455))::(Some (false ),uu____4456)::[]
                      -> arg
                  | uu____4497 -> tm
                else
                  (let uu____4507 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4507
                   then
                     let uu____4508 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4508 with
                     | uu____4541::(Some (true ),uu____4542)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4580)::uu____4581::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4619)::(uu____4620,(arg,uu____4622))::[]
                         -> arg
                     | uu____4663 -> tm
                   else
                     (let uu____4673 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4673
                      then
                        let uu____4674 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4674 with
                        | (Some (true ),uu____4707)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4731)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4755 -> tm
                      else
                        (let uu____4765 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4765
                         then
                           match args with
                           | (t,uu____4767)::[] ->
                               let uu____4780 =
                                 let uu____4781 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4781.FStar_Syntax_Syntax.n in
                               (match uu____4780 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4784::[],body,uu____4786) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4812 -> tm)
                                | uu____4814 -> tm)
                           | (uu____4815,Some (FStar_Syntax_Syntax.Implicit
                              uu____4816))::(t,uu____4818)::[] ->
                               let uu____4845 =
                                 let uu____4846 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4846.FStar_Syntax_Syntax.n in
                               (match uu____4845 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4849::[],body,uu____4851) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4877 -> tm)
                                | uu____4879 -> tm)
                           | uu____4880 -> tm
                         else
                           (let uu____4887 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4887
                            then
                              match args with
                              | (t,uu____4889)::[] ->
                                  let uu____4902 =
                                    let uu____4903 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4903.FStar_Syntax_Syntax.n in
                                  (match uu____4902 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4906::[],body,uu____4908) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4934 -> tm)
                                   | uu____4936 -> tm)
                              | (uu____4937,Some
                                 (FStar_Syntax_Syntax.Implicit uu____4938))::
                                  (t,uu____4940)::[] ->
                                  let uu____4967 =
                                    let uu____4968 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4968.FStar_Syntax_Syntax.n in
                                  (match uu____4967 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4971::[],body,uu____4973) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4999 -> tm)
                                   | uu____5001 -> tm)
                              | uu____5002 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5010;
                FStar_Syntax_Syntax.pos = uu____5011;
                FStar_Syntax_Syntax.vars = uu____5012;_},args)
             ->
             let uu____5028 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5028
             then
               let uu____5029 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5029 with
                | (Some (true ),uu____5062)::(uu____5063,(arg,uu____5065))::[]
                    -> arg
                | (uu____5106,(arg,uu____5108))::(Some (true ),uu____5109)::[]
                    -> arg
                | (Some (false ),uu____5150)::uu____5151::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5189::(Some (false ),uu____5190)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5228 -> tm)
             else
               (let uu____5238 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5238
                then
                  let uu____5239 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5239 with
                  | (Some (true ),uu____5272)::uu____5273::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5311::(Some (true ),uu____5312)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5350)::(uu____5351,(arg,uu____5353))::[]
                      -> arg
                  | (uu____5394,(arg,uu____5396))::(Some (false ),uu____5397)::[]
                      -> arg
                  | uu____5438 -> tm
                else
                  (let uu____5448 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5448
                   then
                     let uu____5449 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5449 with
                     | uu____5482::(Some (true ),uu____5483)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5521)::uu____5522::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5560)::(uu____5561,(arg,uu____5563))::[]
                         -> arg
                     | uu____5604 -> tm
                   else
                     (let uu____5614 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5614
                      then
                        let uu____5615 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5615 with
                        | (Some (true ),uu____5648)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5672)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5696 -> tm
                      else
                        (let uu____5706 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5706
                         then
                           match args with
                           | (t,uu____5708)::[] ->
                               let uu____5721 =
                                 let uu____5722 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5722.FStar_Syntax_Syntax.n in
                               (match uu____5721 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5725::[],body,uu____5727) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5753 -> tm)
                                | uu____5755 -> tm)
                           | (uu____5756,Some (FStar_Syntax_Syntax.Implicit
                              uu____5757))::(t,uu____5759)::[] ->
                               let uu____5786 =
                                 let uu____5787 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5787.FStar_Syntax_Syntax.n in
                               (match uu____5786 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5790::[],body,uu____5792) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5818 -> tm)
                                | uu____5820 -> tm)
                           | uu____5821 -> tm
                         else
                           (let uu____5828 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5828
                            then
                              match args with
                              | (t,uu____5830)::[] ->
                                  let uu____5843 =
                                    let uu____5844 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5844.FStar_Syntax_Syntax.n in
                                  (match uu____5843 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5847::[],body,uu____5849) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5875 -> tm)
                                   | uu____5877 -> tm)
                              | (uu____5878,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5879))::
                                  (t,uu____5881)::[] ->
                                  let uu____5908 =
                                    let uu____5909 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5909.FStar_Syntax_Syntax.n in
                                  (match uu____5908 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5912::[],body,uu____5914) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5940 -> tm)
                                   | uu____5942 -> tm)
                              | uu____5943 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5950 -> tm)
let is_norm_request hd1 args =
  let uu____5965 =
    let uu____5969 =
      let uu____5970 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5970.FStar_Syntax_Syntax.n in
    (uu____5969, args) in
  match uu____5965 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5975::uu____5976::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5979::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____5981 -> false
let get_norm_request args =
  match args with
  | uu____6000::(tm,uu____6002)::[] -> tm
  | (tm,uu____6012)::[] -> tm
  | uu____6017 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___136_6024  ->
    match uu___136_6024 with
=======
                     FStar_Syntax_Syntax.tk = uu____4081;
                     FStar_Syntax_Syntax.pos = uu____4082;
                     FStar_Syntax_Syntax.vars = uu____4083;_},uu____4084);
                FStar_Syntax_Syntax.tk = uu____4085;
                FStar_Syntax_Syntax.pos = uu____4086;
                FStar_Syntax_Syntax.vars = uu____4087;_},args)
             ->
             let uu____4107 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____4107
             then
               let uu____4108 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____4108 with
                | (Some (true ),uu____4141)::(uu____4142,(arg,uu____4144))::[]
                    -> arg
                | (uu____4185,(arg,uu____4187))::(Some (true ),uu____4188)::[]
                    -> arg
                | (Some (false ),uu____4229)::uu____4230::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4268::(Some (false ),uu____4269)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____4307 -> tm)
             else
               (let uu____4317 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____4317
                then
                  let uu____4318 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____4318 with
                  | (Some (true ),uu____4351)::uu____4352::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____4390::(Some (true ),uu____4391)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____4429)::(uu____4430,(arg,uu____4432))::[]
                      -> arg
                  | (uu____4473,(arg,uu____4475))::(Some (false ),uu____4476)::[]
                      -> arg
                  | uu____4517 -> tm
                else
                  (let uu____4527 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____4527
                   then
                     let uu____4528 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____4528 with
                     | uu____4561::(Some (true ),uu____4562)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____4600)::uu____4601::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____4639)::(uu____4640,(arg,uu____4642))::[]
                         -> arg
                     | uu____4683 -> tm
                   else
                     (let uu____4693 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____4693
                      then
                        let uu____4694 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____4694 with
                        | (Some (true ),uu____4727)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____4751)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____4775 -> tm
                      else
                        (let uu____4785 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____4785
                         then
                           match args with
                           | (t,uu____4787)::[] ->
                               let uu____4800 =
                                 let uu____4801 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4801.FStar_Syntax_Syntax.n in
                               (match uu____4800 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4804::[],body,uu____4806) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4832 -> tm)
                                | uu____4834 -> tm)
                           | (uu____4835,Some (FStar_Syntax_Syntax.Implicit
                              uu____4836))::(t,uu____4838)::[] ->
                               let uu____4865 =
                                 let uu____4866 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____4866.FStar_Syntax_Syntax.n in
                               (match uu____4865 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____4869::[],body,uu____4871) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____4897 -> tm)
                                | uu____4899 -> tm)
                           | uu____4900 -> tm
                         else
                           (let uu____4907 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____4907
                            then
                              match args with
                              | (t,uu____4909)::[] ->
                                  let uu____4922 =
                                    let uu____4923 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4923.FStar_Syntax_Syntax.n in
                                  (match uu____4922 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4926::[],body,uu____4928) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____4954 -> tm)
                                   | uu____4956 -> tm)
                              | (uu____4957,Some
                                 (FStar_Syntax_Syntax.Implicit uu____4958))::
                                  (t,uu____4960)::[] ->
                                  let uu____4987 =
                                    let uu____4988 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4988.FStar_Syntax_Syntax.n in
                                  (match uu____4987 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____4991::[],body,uu____4993) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5019 -> tm)
                                   | uu____5021 -> tm)
                              | uu____5022 -> tm
                            else reduce_equality cfg tm)))))
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____5030;
                FStar_Syntax_Syntax.pos = uu____5031;
                FStar_Syntax_Syntax.vars = uu____5032;_},args)
             ->
             let uu____5048 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid in
             if uu____5048
             then
               let uu____5049 =
                 FStar_All.pipe_right args (FStar_List.map simplify) in
               (match uu____5049 with
                | (Some (true ),uu____5082)::(uu____5083,(arg,uu____5085))::[]
                    -> arg
                | (uu____5126,(arg,uu____5128))::(Some (true ),uu____5129)::[]
                    -> arg
                | (Some (false ),uu____5170)::uu____5171::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5209::(Some (false ),uu____5210)::[] ->
                    w FStar_Syntax_Util.t_false
                | uu____5248 -> tm)
             else
               (let uu____5258 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid in
                if uu____5258
                then
                  let uu____5259 =
                    FStar_All.pipe_right args (FStar_List.map simplify) in
                  match uu____5259 with
                  | (Some (true ),uu____5292)::uu____5293::[] ->
                      w FStar_Syntax_Util.t_true
                  | uu____5331::(Some (true ),uu____5332)::[] ->
                      w FStar_Syntax_Util.t_true
                  | (Some (false ),uu____5370)::(uu____5371,(arg,uu____5373))::[]
                      -> arg
                  | (uu____5414,(arg,uu____5416))::(Some (false ),uu____5417)::[]
                      -> arg
                  | uu____5458 -> tm
                else
                  (let uu____5468 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.imp_lid in
                   if uu____5468
                   then
                     let uu____5469 =
                       FStar_All.pipe_right args (FStar_List.map simplify) in
                     match uu____5469 with
                     | uu____5502::(Some (true ),uu____5503)::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (false ),uu____5541)::uu____5542::[] ->
                         w FStar_Syntax_Util.t_true
                     | (Some (true ),uu____5580)::(uu____5581,(arg,uu____5583))::[]
                         -> arg
                     | uu____5624 -> tm
                   else
                     (let uu____5634 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.not_lid in
                      if uu____5634
                      then
                        let uu____5635 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        match uu____5635 with
                        | (Some (true ),uu____5668)::[] ->
                            w FStar_Syntax_Util.t_false
                        | (Some (false ),uu____5692)::[] ->
                            w FStar_Syntax_Util.t_true
                        | uu____5716 -> tm
                      else
                        (let uu____5726 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Syntax_Const.forall_lid in
                         if uu____5726
                         then
                           match args with
                           | (t,uu____5728)::[] ->
                               let uu____5741 =
                                 let uu____5742 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5742.FStar_Syntax_Syntax.n in
                               (match uu____5741 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5745::[],body,uu____5747) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5773 -> tm)
                                | uu____5775 -> tm)
                           | (uu____5776,Some (FStar_Syntax_Syntax.Implicit
                              uu____5777))::(t,uu____5779)::[] ->
                               let uu____5806 =
                                 let uu____5807 =
                                   FStar_Syntax_Subst.compress t in
                                 uu____5807.FStar_Syntax_Syntax.n in
                               (match uu____5806 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____5810::[],body,uu____5812) ->
                                    (match simp_t body with
                                     | Some (true ) ->
                                         w FStar_Syntax_Util.t_true
                                     | uu____5838 -> tm)
                                | uu____5840 -> tm)
                           | uu____5841 -> tm
                         else
                           (let uu____5848 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Syntax_Const.exists_lid in
                            if uu____5848
                            then
                              match args with
                              | (t,uu____5850)::[] ->
                                  let uu____5863 =
                                    let uu____5864 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5864.FStar_Syntax_Syntax.n in
                                  (match uu____5863 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5867::[],body,uu____5869) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5895 -> tm)
                                   | uu____5897 -> tm)
                              | (uu____5898,Some
                                 (FStar_Syntax_Syntax.Implicit uu____5899))::
                                  (t,uu____5901)::[] ->
                                  let uu____5928 =
                                    let uu____5929 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____5929.FStar_Syntax_Syntax.n in
                                  (match uu____5928 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____5932::[],body,uu____5934) ->
                                       (match simp_t body with
                                        | Some (false ) ->
                                            w FStar_Syntax_Util.t_false
                                        | uu____5960 -> tm)
                                   | uu____5962 -> tm)
                              | uu____5963 -> tm
                            else reduce_equality cfg tm)))))
         | uu____5970 -> tm)
let is_norm_request hd1 args =
  let uu____5985 =
    let uu____5989 =
      let uu____5990 = FStar_Syntax_Util.un_uinst hd1 in
      uu____5990.FStar_Syntax_Syntax.n in
    (uu____5989, args) in
  match uu____5985 with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5995::uu____5996::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5999::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize
  | uu____6001 -> false
let get_norm_request args =
  match args with
  | uu____6020::(tm,uu____6022)::[] -> tm
  | (tm,uu____6032)::[] -> tm
  | uu____6037 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___135_6044  ->
    match uu___135_6044 with
>>>>>>> origin/master
    | (App
        ({
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
             (FStar_Const.Const_reify );
<<<<<<< HEAD
           FStar_Syntax_Syntax.tk = uu____6026;
           FStar_Syntax_Syntax.pos = uu____6027;
           FStar_Syntax_Syntax.vars = uu____6028;_},uu____6029,uu____6030))::uu____6031
        -> true
    | uu____6037 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6042 =
      let uu____6043 = FStar_Syntax_Util.un_uinst t in
      uu____6043.FStar_Syntax_Syntax.n in
    match uu____6042 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6047 -> false
=======
           FStar_Syntax_Syntax.tk = uu____6046;
           FStar_Syntax_Syntax.pos = uu____6047;
           FStar_Syntax_Syntax.vars = uu____6048;_},uu____6049,uu____6050))::uu____6051
        -> true
    | uu____6057 -> false
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6062 =
      let uu____6063 = FStar_Syntax_Util.un_uinst t in
      uu____6063.FStar_Syntax_Syntax.n in
    match uu____6062 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_tactics_embed_lid
    | uu____6067 -> false
>>>>>>> origin/master
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
<<<<<<< HEAD
            (fun uu____6161  ->
               let uu____6162 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6163 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6164 =
                 let uu____6165 =
                   let uu____6167 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6167 in
                 stack_to_string uu____6165 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6162
                 uu____6163 uu____6164);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6179 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6200 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6211 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6212 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6213;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6214;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6219;
                 FStar_Syntax_Syntax.fv_delta = uu____6220;
=======
            (fun uu____6181  ->
               let uu____6182 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____6183 = FStar_Syntax_Print.term_to_string t1 in
               let uu____6184 =
                 let uu____6185 =
                   let uu____6187 = firstn (Prims.parse_int "4") stack1 in
                   FStar_All.pipe_left FStar_Pervasives.fst uu____6187 in
                 stack_to_string uu____6185 in
               FStar_Util.print3
                 ">>> %s\nNorm %s with top of the stack %s \n" uu____6182
                 uu____6183 uu____6184);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____6199 ->
               failwith "Impossible"
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_uvar uu____6220 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_constant uu____6229 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_name uu____6230 ->
               rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6231;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____6232;_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____6237;
                 FStar_Syntax_Syntax.fv_delta = uu____6238;
>>>>>>> origin/master
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
               { FStar_Syntax_Syntax.fv_name = uu____6224;
                 FStar_Syntax_Syntax.fv_delta = uu____6225;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6226);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6234;
                  FStar_Syntax_Syntax.pos = uu____6235;
                  FStar_Syntax_Syntax.vars = uu____6236;_},uu____6237)
=======
               { FStar_Syntax_Syntax.fv_name = uu____6242;
                 FStar_Syntax_Syntax.fv_delta = uu____6243;
                 FStar_Syntax_Syntax.fv_qual = Some
                   (FStar_Syntax_Syntax.Record_ctor uu____6244);_}
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.tk = uu____6252;
                  FStar_Syntax_Syntax.pos = uu____6253;
                  FStar_Syntax_Syntax.vars = uu____6254;_},uu____6255)
>>>>>>> origin/master
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Syntax_Const.fstar_tactics_embed_lid
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               is_fstar_tactics_embed hd1 ->
               let args1 = closures_as_args_delayed cfg env args in
               let t2 =
<<<<<<< HEAD
                 let uu___162_6277 = t1 in
=======
                 let uu___160_6295 = t1 in
>>>>>>> origin/master
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args1));
                   FStar_Syntax_Syntax.tk =
<<<<<<< HEAD
                     (uu___162_6277.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___162_6277.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___162_6277.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6306 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6306) && (is_norm_request hd1 args))
=======
                     (uu___160_6295.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___160_6295.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___160_6295.FStar_Syntax_Syntax.vars)
                 } in
               let t3 = reduce_primops cfg t2 in rebuild cfg env stack1 t3
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____6324 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____6324) && (is_norm_request hd1 args))
>>>>>>> origin/master
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
<<<<<<< HEAD
                 let uu___163_6319 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___163_6319.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___163_6319.primitive_steps)
=======
                 let uu___161_6337 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___161_6337.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___161_6337.primitive_steps)
>>>>>>> origin/master
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
<<<<<<< HEAD
                  FStar_Syntax_Syntax.tk = uu____6324;
                  FStar_Syntax_Syntax.pos = uu____6325;
                  FStar_Syntax_Syntax.vars = uu____6326;_},a1::a2::rest)
               ->
               let uu____6360 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6360 with
                | (hd1,uu____6371) ->
=======
                  FStar_Syntax_Syntax.tk = uu____6342;
                  FStar_Syntax_Syntax.pos = uu____6343;
                  FStar_Syntax_Syntax.vars = uu____6344;_},a1::a2::rest)
               ->
               let uu____6378 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6378 with
                | (hd1,uu____6389) ->
>>>>>>> origin/master
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
<<<<<<< HEAD
                    (FStar_Const.Const_reflect uu____6426);
                  FStar_Syntax_Syntax.tk = uu____6427;
                  FStar_Syntax_Syntax.pos = uu____6428;
                  FStar_Syntax_Syntax.vars = uu____6429;_},a::[])
=======
                    (FStar_Const.Const_reflect uu____6444);
                  FStar_Syntax_Syntax.tk = uu____6445;
                  FStar_Syntax_Syntax.pos = uu____6446;
                  FStar_Syntax_Syntax.vars = uu____6447;_},a::[])
>>>>>>> origin/master
               when
               (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
                 && (is_reify_head stack1)
               ->
<<<<<<< HEAD
               let uu____6452 = FStar_List.tl stack1 in
               norm cfg env uu____6452 (fst a)
=======
               let uu____6470 = FStar_List.tl stack1 in
               norm cfg env uu____6470 (fst a)
>>>>>>> origin/master
           | FStar_Syntax_Syntax.Tm_app
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify );
<<<<<<< HEAD
                  FStar_Syntax_Syntax.tk = uu____6455;
                  FStar_Syntax_Syntax.pos = uu____6456;
                  FStar_Syntax_Syntax.vars = uu____6457;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6480 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6480 with
                | (reify_head,uu____6491) ->
                    let a1 =
                      let uu____6507 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6507 in
=======
                  FStar_Syntax_Syntax.tk = uu____6473;
                  FStar_Syntax_Syntax.pos = uu____6474;
                  FStar_Syntax_Syntax.vars = uu____6475;_},a::[])
               when
               FStar_All.pipe_right cfg.steps (FStar_List.contains Reify) ->
               let uu____6498 = FStar_Syntax_Util.head_and_args t1 in
               (match uu____6498 with
                | (reify_head,uu____6509) ->
                    let a1 =
                      let uu____6525 =
                        FStar_All.pipe_left FStar_Syntax_Util.unascribe
                          (fst a) in
                      FStar_Syntax_Subst.compress uu____6525 in
>>>>>>> origin/master
                    (match a1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_constant
<<<<<<< HEAD
                              (FStar_Const.Const_reflect uu____6510);
                            FStar_Syntax_Syntax.tk = uu____6511;
                            FStar_Syntax_Syntax.pos = uu____6512;
                            FStar_Syntax_Syntax.vars = uu____6513;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6538 ->
=======
                              (FStar_Const.Const_reflect uu____6528);
                            FStar_Syntax_Syntax.tk = uu____6529;
                            FStar_Syntax_Syntax.pos = uu____6530;
                            FStar_Syntax_Syntax.vars = uu____6531;_},a2::[])
                         -> norm cfg env stack1 (fst a2)
                     | uu____6556 ->
>>>>>>> origin/master
                         let stack2 =
                           (App
                              (reify_head, None,
                                (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1 in
                         norm cfg env stack2 a1))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
<<<<<<< HEAD
               let uu____6546 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6546
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6553 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6553
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6556 =
                      let uu____6560 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6560, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6556 in
=======
               let uu____6564 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack1 uu____6564
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____6571 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____6571
               then norm cfg env stack1 t'
               else
                 (let us1 =
                    let uu____6574 =
                      let uu____6578 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____6578, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____6574 in
>>>>>>> origin/master
                  let stack2 = us1 :: stack1 in norm cfg env stack2 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let t0 = t1 in
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
<<<<<<< HEAD
                      (fun uu___137_6569  ->
                         match uu___137_6569 with
=======
                      (fun uu___136_6587  ->
                         match uu___136_6587 with
>>>>>>> origin/master
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               if Prims.op_Negation should_delta
               then rebuild cfg env stack1 t1
               else
                 (let r_env =
<<<<<<< HEAD
                    let uu____6573 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6573 in
                  let uu____6574 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6574 with
                  | None  ->
                      (log cfg
                         (fun uu____6585  ->
=======
                    let uu____6591 = FStar_Syntax_Syntax.range_of_fv f in
                    FStar_TypeChecker_Env.set_range cfg.tcenv uu____6591 in
                  let uu____6592 =
                    FStar_TypeChecker_Env.lookup_definition cfg.delta_level
                      r_env
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu____6592 with
                  | None  ->
                      (log cfg
                         (fun uu____6603  ->
>>>>>>> origin/master
                            FStar_Util.print "Tm_fvar case 2\n" []);
                       rebuild cfg env stack1 t1)
                  | Some (us,t2) ->
                      (log cfg
<<<<<<< HEAD
                         (fun uu____6591  ->
                            let uu____6592 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6593 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6592 uu____6593);
                       (let t3 =
                          let uu____6595 =
=======
                         (fun uu____6609  ->
                            let uu____6610 =
                              FStar_Syntax_Print.term_to_string t0 in
                            let uu____6611 =
                              FStar_Syntax_Print.term_to_string t2 in
                            FStar_Util.print2 ">>> Unfolded %s to %s\n"
                              uu____6610 uu____6611);
                       (let t3 =
                          let uu____6613 =
>>>>>>> origin/master
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 (UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant)) in
<<<<<<< HEAD
                          if uu____6595
=======
                          if uu____6613
>>>>>>> origin/master
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
<<<<<<< HEAD
                          | (UnivArgs (us',uu____6607))::stack2 ->
=======
                          | (UnivArgs (us',uu____6625))::stack2 ->
>>>>>>> origin/master
                              let env1 =
                                FStar_All.pipe_right us'
                                  (FStar_List.fold_left
                                     (fun env1  -> fun u  -> (Univ u) :: env1)
                                     env) in
                              norm cfg env1 stack2 t3
<<<<<<< HEAD
                          | uu____6620 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6621 ->
                              let uu____6622 =
                                let uu____6623 =
=======
                          | uu____6638 when
                              FStar_All.pipe_right cfg.steps
                                (FStar_List.contains EraseUniverses)
                              -> norm cfg env stack1 t3
                          | uu____6639 ->
                              let uu____6640 =
                                let uu____6641 =
>>>>>>> origin/master
                                  FStar_Syntax_Print.lid_to_string
                                    (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                FStar_Util.format1
                                  "Impossible: missing universe instantiation on %s"
<<<<<<< HEAD
                                  uu____6623 in
                              failwith uu____6622
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6630 = lookup_bvar env x in
               (match uu____6630 with
                | Univ uu____6631 ->
=======
                                  uu____6641 in
                              failwith uu____6640
                        else norm cfg env stack1 t3)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____6648 = lookup_bvar env x in
               (match uu____6648 with
                | Univ uu____6649 ->
>>>>>>> origin/master
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
<<<<<<< HEAD
                      let uu____6646 = FStar_ST.read r in
                      (match uu____6646 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6665  ->
                                 let uu____6666 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6667 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6666
                                   uu____6667);
                            (let uu____6668 =
                               let uu____6669 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6669.FStar_Syntax_Syntax.n in
                             match uu____6668 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6672 ->
                                 norm cfg env2 stack1 t'
                             | uu____6687 -> rebuild cfg env2 stack1 t'))
=======
                      let uu____6664 = FStar_ST.read r in
                      (match uu____6664 with
                       | Some (env2,t') ->
                           (log cfg
                              (fun uu____6683  ->
                                 let uu____6684 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____6685 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____6684
                                   uu____6685);
                            (let uu____6686 =
                               let uu____6687 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____6687.FStar_Syntax_Syntax.n in
                             match uu____6686 with
                             | FStar_Syntax_Syntax.Tm_abs uu____6690 ->
                                 norm cfg env2 stack1 t'
                             | uu____6705 -> rebuild cfg env2 stack1 t'))
>>>>>>> origin/master
                       | None  -> norm cfg env1 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env1 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
<<<<<<< HEAD
                | (UnivArgs uu____6720)::uu____6721 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6726)::uu____6727 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6733,uu____6734))::stack_rest ->
                    (match c with
                     | Univ uu____6737 -> norm cfg (c :: env) stack_rest t1
                     | uu____6738 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6741::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6754  ->
                                         let uu____6755 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6755);
=======
                | (UnivArgs uu____6738)::uu____6739 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____6744)::uu____6745 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____6751,uu____6752))::stack_rest ->
                    (match c with
                     | Univ uu____6755 -> norm cfg (c :: env) stack_rest t1
                     | uu____6756 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | uu____6759::[] ->
                              (match lopt with
                               | None  when FStar_Options.__unit_tests () ->
                                   (log cfg
                                      (fun uu____6772  ->
                                         let uu____6773 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6773);
>>>>>>> origin/master
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
<<<<<<< HEAD
                                           (fun uu___138_6769  ->
                                              match uu___138_6769 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6770 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6772  ->
                                         let uu____6773 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6773);
=======
                                           (fun uu___137_6787  ->
                                              match uu___137_6787 with
                                              | FStar_Syntax_Syntax.TOTAL  ->
                                                  true
                                              | uu____6788 -> false)))
                                   ->
                                   (log cfg
                                      (fun uu____6790  ->
                                         let uu____6791 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6791);
>>>>>>> origin/master
                                    norm cfg (c :: env) stack_rest body)
                               | Some (FStar_Util.Inl lc) when
                                   FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                                   ->
                                   (log cfg
<<<<<<< HEAD
                                      (fun uu____6784  ->
                                         let uu____6785 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6785);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6786 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6793 ->
                                   let cfg1 =
                                     let uu___164_6801 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___164_6801.tcenv);
                                       delta_level =
                                         (uu___164_6801.delta_level);
                                       primitive_steps =
                                         (uu___164_6801.primitive_steps)
                                     } in
                                   let uu____6802 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6802)
                          | uu____6803::tl1 ->
                              (log cfg
                                 (fun uu____6813  ->
                                    let uu____6814 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6814);
=======
                                      (fun uu____6802  ->
                                         let uu____6803 = closure_to_string c in
                                         FStar_Util.print1 "\tShifted %s\n"
                                           uu____6803);
                                    norm cfg (c :: env) stack_rest body)
                               | uu____6804 when
                                   FStar_All.pipe_right cfg.steps
                                     (FStar_List.contains Reify)
                                   -> norm cfg (c :: env) stack_rest body
                               | uu____6811 ->
                                   let cfg1 =
                                     let uu___162_6819 = cfg in
                                     {
                                       steps = (WHNF :: (Exclude Iota) ::
                                         (Exclude Zeta) :: (cfg.steps));
                                       tcenv = (uu___162_6819.tcenv);
                                       delta_level =
                                         (uu___162_6819.delta_level);
                                       primitive_steps =
                                         (uu___162_6819.primitive_steps)
                                     } in
                                   let uu____6820 =
                                     closure_as_term cfg1 env t1 in
                                   rebuild cfg1 env stack1 uu____6820)
                          | uu____6821::tl1 ->
                              (log cfg
                                 (fun uu____6831  ->
                                    let uu____6832 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____6832);
>>>>>>> origin/master
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg (c :: env) stack_rest body1))))
                | (Steps (s,ps,dl))::stack2 ->
                    norm
<<<<<<< HEAD
                      (let uu___165_6838 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___165_6838.tcenv);
=======
                      (let uu___163_6856 = cfg in
                       {
                         steps = s;
                         tcenv = (uu___163_6856.tcenv);
>>>>>>> origin/master
                         delta_level = dl;
                         primitive_steps = ps
                       }) env stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo r (env, t1);
                     log cfg
<<<<<<< HEAD
                       (fun uu____6851  ->
                          let uu____6852 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6852);
                     norm cfg env stack2 t1)
                | (Debug uu____6853)::uu____6854 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6856 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6856
                    else
                      (let uu____6858 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6858 with
=======
                       (fun uu____6869  ->
                          let uu____6870 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____6870);
                     norm cfg env stack2 t1)
                | (Debug uu____6871)::uu____6872 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6874 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6874
                    else
                      (let uu____6876 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6876 with
>>>>>>> origin/master
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
<<<<<<< HEAD
                                 let uu____6887 =
                                   let uu____6893 =
                                     let uu____6894 =
                                       let uu____6895 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6895 in
                                     FStar_All.pipe_right uu____6894
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6893
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6887
                                   (fun _0_32  -> Some _0_32)
                             | uu____6920 -> lopt in
=======
                                 let uu____6905 =
                                   let uu____6911 =
                                     let uu____6912 =
                                       let uu____6913 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____6913 in
                                     FStar_All.pipe_right uu____6912
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____6911
                                     (fun _0_31  -> FStar_Util.Inl _0_31) in
                                 FStar_All.pipe_right uu____6905
                                   (fun _0_32  -> Some _0_32)
                             | uu____6938 -> lopt in
>>>>>>> origin/master
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____6934  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6939  ->
                                 let uu____6940 =
=======
                                     fun uu____6952  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____6957  ->
                                 let uu____6958 =
>>>>>>> origin/master
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
<<<<<<< HEAD
                                   uu____6940);
=======
                                   uu____6958);
>>>>>>> origin/master
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___166_6950 = cfg in
                               let uu____6951 =
=======
                               let uu___164_6968 = cfg in
                               let uu____6969 =
>>>>>>> origin/master
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
<<<<<<< HEAD
                                 steps = (uu___166_6950.steps);
                                 tcenv = (uu___166_6950.tcenv);
                                 delta_level = (uu___166_6950.delta_level);
                                 primitive_steps = uu____6951
=======
                                 steps = (uu___164_6968.steps);
                                 tcenv = (uu___164_6968.tcenv);
                                 delta_level = (uu___164_6968.delta_level);
                                 primitive_steps = uu____6969
>>>>>>> origin/master
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
<<<<<<< HEAD
                | (Meta uu____6961)::uu____6962 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6966 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6966
                    else
                      (let uu____6968 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6968 with
=======
                | (Meta uu____6979)::uu____6980 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____6984 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____6984
                    else
                      (let uu____6986 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____6986 with
>>>>>>> origin/master
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
<<<<<<< HEAD
                                 let uu____6997 =
                                   let uu____7003 =
                                     let uu____7004 =
                                       let uu____7005 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7005 in
                                     FStar_All.pipe_right uu____7004
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7003
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____6997
                                   (fun _0_34  -> Some _0_34)
                             | uu____7030 -> lopt in
=======
                                 let uu____7015 =
                                   let uu____7021 =
                                     let uu____7022 =
                                       let uu____7023 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7023 in
                                     FStar_All.pipe_right uu____7022
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7021
                                     (fun _0_33  -> FStar_Util.Inl _0_33) in
                                 FStar_All.pipe_right uu____7015
                                   (fun _0_34  -> Some _0_34)
                             | uu____7048 -> lopt in
>>>>>>> origin/master
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____7044  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7049  ->
                                 let uu____7050 =
=======
                                     fun uu____7062  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7067  ->
                                 let uu____7068 =
>>>>>>> origin/master
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
<<<<<<< HEAD
                                   uu____7050);
=======
                                   uu____7068);
>>>>>>> origin/master
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___166_7060 = cfg in
                               let uu____7061 =
=======
                               let uu___164_7078 = cfg in
                               let uu____7079 =
>>>>>>> origin/master
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
<<<<<<< HEAD
                                 steps = (uu___166_7060.steps);
                                 tcenv = (uu___166_7060.tcenv);
                                 delta_level = (uu___166_7060.delta_level);
                                 primitive_steps = uu____7061
=======
                                 steps = (uu___164_7078.steps);
                                 tcenv = (uu___164_7078.tcenv);
                                 delta_level = (uu___164_7078.delta_level);
                                 primitive_steps = uu____7079
>>>>>>> origin/master
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
<<<<<<< HEAD
                | (Let uu____7071)::uu____7072 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7078 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7078
                    else
                      (let uu____7080 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7080 with
=======
                | (Let uu____7089)::uu____7090 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7096 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7096
                    else
                      (let uu____7098 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7098 with
>>>>>>> origin/master
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
<<<<<<< HEAD
                                 let uu____7109 =
                                   let uu____7115 =
                                     let uu____7116 =
                                       let uu____7117 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7117 in
                                     FStar_All.pipe_right uu____7116
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7115
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7109
                                   (fun _0_36  -> Some _0_36)
                             | uu____7142 -> lopt in
=======
                                 let uu____7127 =
                                   let uu____7133 =
                                     let uu____7134 =
                                       let uu____7135 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7135 in
                                     FStar_All.pipe_right uu____7134
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7133
                                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                                 FStar_All.pipe_right uu____7127
                                   (fun _0_36  -> Some _0_36)
                             | uu____7160 -> lopt in
>>>>>>> origin/master
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____7156  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7161  ->
                                 let uu____7162 =
=======
                                     fun uu____7174  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7179  ->
                                 let uu____7180 =
>>>>>>> origin/master
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
<<<<<<< HEAD
                                   uu____7162);
=======
                                   uu____7180);
>>>>>>> origin/master
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___166_7172 = cfg in
                               let uu____7173 =
=======
                               let uu___164_7190 = cfg in
                               let uu____7191 =
>>>>>>> origin/master
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
<<<<<<< HEAD
                                 steps = (uu___166_7172.steps);
                                 tcenv = (uu___166_7172.tcenv);
                                 delta_level = (uu___166_7172.delta_level);
                                 primitive_steps = uu____7173
=======
                                 steps = (uu___164_7190.steps);
                                 tcenv = (uu___164_7190.tcenv);
                                 delta_level = (uu___164_7190.delta_level);
                                 primitive_steps = uu____7191
>>>>>>> origin/master
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
<<<<<<< HEAD
                | (App uu____7183)::uu____7184 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7189 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7189
                    else
                      (let uu____7191 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7191 with
=======
                | (App uu____7201)::uu____7202 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7207 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7207
                    else
                      (let uu____7209 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7209 with
>>>>>>> origin/master
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
<<<<<<< HEAD
                                 let uu____7220 =
                                   let uu____7226 =
                                     let uu____7227 =
                                       let uu____7228 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7228 in
                                     FStar_All.pipe_right uu____7227
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7226
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7220
                                   (fun _0_38  -> Some _0_38)
                             | uu____7253 -> lopt in
=======
                                 let uu____7238 =
                                   let uu____7244 =
                                     let uu____7245 =
                                       let uu____7246 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7246 in
                                     FStar_All.pipe_right uu____7245
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7244
                                     (fun _0_37  -> FStar_Util.Inl _0_37) in
                                 FStar_All.pipe_right uu____7238
                                   (fun _0_38  -> Some _0_38)
                             | uu____7271 -> lopt in
>>>>>>> origin/master
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____7267  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7272  ->
                                 let uu____7273 =
=======
                                     fun uu____7285  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7290  ->
                                 let uu____7291 =
>>>>>>> origin/master
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
<<<<<<< HEAD
                                   uu____7273);
=======
                                   uu____7291);
>>>>>>> origin/master
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___166_7283 = cfg in
                               let uu____7284 =
=======
                               let uu___164_7301 = cfg in
                               let uu____7302 =
>>>>>>> origin/master
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
<<<<<<< HEAD
                                 steps = (uu___166_7283.steps);
                                 tcenv = (uu___166_7283.tcenv);
                                 delta_level = (uu___166_7283.delta_level);
                                 primitive_steps = uu____7284
=======
                                 steps = (uu___164_7301.steps);
                                 tcenv = (uu___164_7301.tcenv);
                                 delta_level = (uu___164_7301.delta_level);
                                 primitive_steps = uu____7302
>>>>>>> origin/master
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
<<<<<<< HEAD
                | (Abs uu____7294)::uu____7295 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7305 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7305
                    else
                      (let uu____7307 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7307 with
=======
                | (Abs uu____7312)::uu____7313 ->
                    if FStar_List.contains WHNF cfg.steps
                    then
                      let uu____7323 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7323
                    else
                      (let uu____7325 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7325 with
>>>>>>> origin/master
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
<<<<<<< HEAD
                                 let uu____7336 =
                                   let uu____7342 =
                                     let uu____7343 =
                                       let uu____7344 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7344 in
                                     FStar_All.pipe_right uu____7343
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7342
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7336
                                   (fun _0_40  -> Some _0_40)
                             | uu____7369 -> lopt in
=======
                                 let uu____7354 =
                                   let uu____7360 =
                                     let uu____7361 =
                                       let uu____7362 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7362 in
                                     FStar_All.pipe_right uu____7361
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7360
                                     (fun _0_39  -> FStar_Util.Inl _0_39) in
                                 FStar_All.pipe_right uu____7354
                                   (fun _0_40  -> Some _0_40)
                             | uu____7387 -> lopt in
>>>>>>> origin/master
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____7383  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7388  ->
                                 let uu____7389 =
=======
                                     fun uu____7401  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7406  ->
                                 let uu____7407 =
>>>>>>> origin/master
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
<<<<<<< HEAD
                                   uu____7389);
=======
                                   uu____7407);
>>>>>>> origin/master
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___166_7399 = cfg in
                               let uu____7400 =
=======
                               let uu___164_7417 = cfg in
                               let uu____7418 =
>>>>>>> origin/master
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
<<<<<<< HEAD
                                 steps = (uu___166_7399.steps);
                                 tcenv = (uu___166_7399.tcenv);
                                 delta_level = (uu___166_7399.delta_level);
                                 primitive_steps = uu____7400
=======
                                 steps = (uu___164_7417.steps);
                                 tcenv = (uu___164_7417.tcenv);
                                 delta_level = (uu___164_7417.delta_level);
                                 primitive_steps = uu____7418
>>>>>>> origin/master
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if FStar_List.contains WHNF cfg.steps
                    then
<<<<<<< HEAD
                      let uu____7410 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7410
                    else
                      (let uu____7412 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7412 with
=======
                      let uu____7428 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7428
                    else
                      (let uu____7430 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____7430 with
>>>>>>> origin/master
                       | (bs1,body1,opening) ->
                           let lopt1 =
                             match lopt with
                             | Some (FStar_Util.Inl l) ->
<<<<<<< HEAD
                                 let uu____7441 =
                                   let uu____7447 =
                                     let uu____7448 =
                                       let uu____7449 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7449 in
                                     FStar_All.pipe_right uu____7448
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7447
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7441
                                   (fun _0_42  -> Some _0_42)
                             | uu____7474 -> lopt in
=======
                                 let uu____7459 =
                                   let uu____7465 =
                                     let uu____7466 =
                                       let uu____7467 =
                                         l.FStar_Syntax_Syntax.comp () in
                                       FStar_Syntax_Subst.subst_comp opening
                                         uu____7467 in
                                     FStar_All.pipe_right uu____7466
                                       FStar_Syntax_Util.lcomp_of_comp in
                                   FStar_All.pipe_right uu____7465
                                     (fun _0_41  -> FStar_Util.Inl _0_41) in
                                 FStar_All.pipe_right uu____7459
                                   (fun _0_42  -> Some _0_42)
                             | uu____7492 -> lopt in
>>>>>>> origin/master
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
<<<<<<< HEAD
                                     fun uu____7488  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7493  ->
                                 let uu____7494 =
=======
                                     fun uu____7506  -> Dummy :: env1) env) in
                           (log cfg
                              (fun uu____7511  ->
                                 let uu____7512 =
>>>>>>> origin/master
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
<<<<<<< HEAD
                                   uu____7494);
=======
                                   uu____7512);
>>>>>>> origin/master
                            (let stack2 =
                               (Steps
                                  ((cfg.steps), (cfg.primitive_steps),
                                    (cfg.delta_level)))
                               :: stack1 in
                             let cfg1 =
<<<<<<< HEAD
                               let uu___166_7504 = cfg in
                               let uu____7505 =
=======
                               let uu___164_7522 = cfg in
                               let uu____7523 =
>>>>>>> origin/master
                                 FStar_List.filter
                                   (fun ps  -> ps.strong_reduction_ok)
                                   cfg.primitive_steps in
                               {
<<<<<<< HEAD
                                 steps = (uu___166_7504.steps);
                                 tcenv = (uu___166_7504.tcenv);
                                 delta_level = (uu___166_7504.delta_level);
                                 primitive_steps = uu____7505
=======
                                 steps = (uu___164_7522.steps);
                                 tcenv = (uu___164_7522.tcenv);
                                 delta_level = (uu___164_7522.delta_level);
                                 primitive_steps = uu____7523
>>>>>>> origin/master
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
<<<<<<< HEAD
                      (fun uu____7537  ->
                         fun stack2  ->
                           match uu____7537 with
                           | (a,aq) ->
                               let uu____7545 =
                                 let uu____7546 =
                                   let uu____7550 =
                                     let uu____7551 =
                                       let uu____7561 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7561, false) in
                                     Clos uu____7551 in
                                   (uu____7550, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7546 in
                               uu____7545 :: stack2) args) in
               (log cfg
                  (fun uu____7583  ->
                     let uu____7584 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7584);
=======
                      (fun uu____7555  ->
                         fun stack2  ->
                           match uu____7555 with
                           | (a,aq) ->
                               let uu____7563 =
                                 let uu____7564 =
                                   let uu____7568 =
                                     let uu____7569 =
                                       let uu____7579 =
                                         FStar_Util.mk_ref None in
                                       (env, a, uu____7579, false) in
                                     Clos uu____7569 in
                                   (uu____7568, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____7564 in
                               uu____7563 :: stack2) args) in
               (log cfg
                  (fun uu____7601  ->
                     let uu____7602 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____7602);
>>>>>>> origin/master
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
<<<<<<< HEAD
                             ((let uu___167_7605 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___167_7605.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___167_7605.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7606 ->
                      let uu____7609 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7609)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7612 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7612 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7628 =
                          let uu____7629 =
                            let uu____7634 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___168_7635 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___168_7635.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___168_7635.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7634) in
                          FStar_Syntax_Syntax.Tm_refine uu____7629 in
                        mk uu____7628 t1.FStar_Syntax_Syntax.pos in
=======
                             ((let uu___165_7623 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___165_7623.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___165_7623.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack1 t2
                  | uu____7624 ->
                      let uu____7627 = closure_as_term cfg env t1 in
                      rebuild cfg env stack1 uu____7627)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____7630 = FStar_Syntax_Subst.open_term [(x, None)] f in
                  match uu____7630 with
                  | (closing,f1) ->
                      let f2 = norm cfg (Dummy :: env) [] f1 in
                      let t2 =
                        let uu____7646 =
                          let uu____7647 =
                            let uu____7652 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___166_7653 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___166_7653.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___166_7653.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____7652) in
                          FStar_Syntax_Syntax.Tm_refine uu____7647 in
                        mk uu____7646 t1.FStar_Syntax_Syntax.pos in
>>>>>>> origin/master
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains WHNF cfg.steps
               then
<<<<<<< HEAD
                 let uu____7648 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7648
               else
                 (let uu____7650 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7650 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7656 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7662  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7656 c1 in
                      let t2 =
                        let uu____7669 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7669 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7712)::uu____7713 -> norm cfg env stack1 t11
                | (Arg uu____7718)::uu____7719 -> norm cfg env stack1 t11
=======
                 let uu____7666 = closure_as_term cfg env t1 in
                 rebuild cfg env stack1 uu____7666
               else
                 (let uu____7668 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____7668 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____7674 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  -> fun uu____7680  -> Dummy :: env1)
                               env) in
                        norm_comp cfg uu____7674 c1 in
                      let t2 =
                        let uu____7687 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____7687 c2 in
                      rebuild cfg env stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____7730)::uu____7731 -> norm cfg env stack1 t11
                | (Arg uu____7736)::uu____7737 -> norm cfg env stack1 t11
>>>>>>> origin/master
                | (App
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
<<<<<<< HEAD
                       FStar_Syntax_Syntax.tk = uu____7724;
                       FStar_Syntax_Syntax.pos = uu____7725;
                       FStar_Syntax_Syntax.vars = uu____7726;_},uu____7727,uu____7728))::uu____7729
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7735)::uu____7736 ->
                    norm cfg env stack1 t11
                | uu____7741 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7744  ->
=======
                       FStar_Syntax_Syntax.tk = uu____7742;
                       FStar_Syntax_Syntax.pos = uu____7743;
                       FStar_Syntax_Syntax.vars = uu____7744;_},uu____7745,uu____7746))::uu____7747
                    -> norm cfg env stack1 t11
                | (MemoLazy uu____7753)::uu____7754 ->
                    norm cfg env stack1 t11
                | uu____7759 ->
                    let t12 = norm cfg env [] t11 in
                    (log cfg
                       (fun uu____7762  ->
>>>>>>> origin/master
                          FStar_Util.print_string
                            "+++ Normalizing ascription \n");
                     (let tc1 =
                        match tc with
                        | FStar_Util.Inl t2 ->
<<<<<<< HEAD
                            let uu____7757 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7757
                        | FStar_Util.Inr c ->
                            let uu____7765 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7765 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7770 =
=======
                            let uu____7775 = norm cfg env [] t2 in
                            FStar_Util.Inl uu____7775
                        | FStar_Util.Inr c ->
                            let uu____7783 = norm_comp cfg env c in
                            FStar_Util.Inr uu____7783 in
                      let tacopt1 =
                        FStar_Util.map_opt tacopt (norm cfg env []) in
                      let uu____7788 =
>>>>>>> origin/master
                        mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (t12, (tc1, tacopt1), l))
                          t1.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
                      rebuild cfg env stack1 uu____7770)))
=======
                      rebuild cfg env stack1 uu____7788)))
>>>>>>> origin/master
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack2 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack1 in
               norm cfg env stack2 head1
           | FStar_Syntax_Syntax.Tm_let
<<<<<<< HEAD
               ((uu____7821,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7822;
                              FStar_Syntax_Syntax.lbunivs = uu____7823;
                              FStar_Syntax_Syntax.lbtyp = uu____7824;
                              FStar_Syntax_Syntax.lbeff = uu____7825;
                              FStar_Syntax_Syntax.lbdef = uu____7826;_}::uu____7827),uu____7828)
=======
               ((uu____7839,{
                              FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                uu____7840;
                              FStar_Syntax_Syntax.lbunivs = uu____7841;
                              FStar_Syntax_Syntax.lbtyp = uu____7842;
                              FStar_Syntax_Syntax.lbeff = uu____7843;
                              FStar_Syntax_Syntax.lbdef = uu____7844;_}::uu____7845),uu____7846)
>>>>>>> origin/master
               -> rebuild cfg env stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
<<<<<<< HEAD
               let uu____7854 =
                 (let uu____7855 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7855) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7856 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7856))) in
               if uu____7854
               then
                 let env1 =
                   let uu____7859 =
                     let uu____7860 =
                       let uu____7870 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7870,
                         false) in
                     Clos uu____7860 in
                   uu____7859 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7894 =
                    let uu____7897 =
                      let uu____7898 =
                        let uu____7899 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7899
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7898] in
                    FStar_Syntax_Subst.open_term uu____7897 body in
                  match uu____7894 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___169_7905 = lb in
                        let uu____7906 =
                          let uu____7909 =
                            let uu____7910 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7910
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7909
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____7919 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7922 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7906;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___169_7905.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7919;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___169_7905.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7922
=======
               let uu____7872 =
                 (let uu____7873 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____7873) &&
                   ((FStar_Syntax_Util.is_pure_effect n1) ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____7874 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____7874))) in
               if uu____7872
               then
                 let env1 =
                   let uu____7877 =
                     let uu____7878 =
                       let uu____7888 = FStar_Util.mk_ref None in
                       (env, (lb.FStar_Syntax_Syntax.lbdef), uu____7888,
                         false) in
                     Clos uu____7878 in
                   uu____7877 :: env in
                 norm cfg env1 stack1 body
               else
                 (let uu____7912 =
                    let uu____7915 =
                      let uu____7916 =
                        let uu____7917 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____7917
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____7916] in
                    FStar_Syntax_Subst.open_term uu____7915 body in
                  match uu____7912 with
                  | (bs,body1) ->
                      let lb1 =
                        let uu___167_7923 = lb in
                        let uu____7924 =
                          let uu____7927 =
                            let uu____7928 = FStar_List.hd bs in
                            FStar_All.pipe_right uu____7928
                              FStar_Pervasives.fst in
                          FStar_All.pipe_right uu____7927
                            (fun _0_43  -> FStar_Util.Inl _0_43) in
                        let uu____7937 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____7940 =
                          norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname = uu____7924;
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___167_7923.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____7937;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___167_7923.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____7940
>>>>>>> origin/master
                        } in
                      let env' =
                        FStar_All.pipe_right bs
                          (FStar_List.fold_left
<<<<<<< HEAD
                             (fun env1  -> fun uu____7932  -> Dummy :: env1)
=======
                             (fun env1  -> fun uu____7950  -> Dummy :: env1)
>>>>>>> origin/master
                             env) in
                      norm cfg env'
                        ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                        :: stack1) body1)
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
<<<<<<< HEAD
               let uu____7948 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7948
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7961 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____7983  ->
                        match uu____7983 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8022 =
                                let uu___170_8023 =
=======
               let uu____7966 = closure_as_term cfg env t1 in
               rebuild cfg env stack1 uu____7966
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____7979 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____8001  ->
                        match uu____8001 with
                        | (rec_env,memos,i) ->
                            let f_i =
                              let uu____8040 =
                                let uu___168_8041 =
>>>>>>> origin/master
                                  FStar_Util.left
                                    lb.FStar_Syntax_Syntax.lbname in
                                {
                                  FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                    (uu___170_8023.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___170_8023.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8022 in
=======
                                    (uu___168_8041.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index = i;
                                  FStar_Syntax_Syntax.sort =
                                    (uu___168_8041.FStar_Syntax_Syntax.sort)
                                } in
                              FStar_Syntax_Syntax.bv_to_tm uu____8040 in
>>>>>>> origin/master
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo = FStar_Util.mk_ref None in
                            let rec_env1 = (Clos (env, fix_f_i, memo, true))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1")))) (snd lbs)
                   (env, [], (Prims.parse_int "0")) in
<<<<<<< HEAD
               (match uu____7961 with
                | (rec_env,memos,uu____8083) ->
                    let uu____8098 =
=======
               (match uu____7979 with
                | (rec_env,memos,uu____8101) ->
                    let uu____8116 =
>>>>>>> origin/master
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
<<<<<<< HEAD
                             let uu____8140 =
                               let uu____8141 =
                                 let uu____8151 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8151, false) in
                               Clos uu____8141 in
                             uu____8140 :: env1) (snd lbs) env in
=======
                             let uu____8158 =
                               let uu____8159 =
                                 let uu____8169 = FStar_Util.mk_ref None in
                                 (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                   uu____8169, false) in
                               Clos uu____8159 in
                             uu____8158 :: env1) (snd lbs) env in
>>>>>>> origin/master
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
<<<<<<< HEAD
                             FStar_Syntax_Syntax.tk = uu____8189;
                             FStar_Syntax_Syntax.pos = uu____8190;
                             FStar_Syntax_Syntax.vars = uu____8191;_},uu____8192,uu____8193))::uu____8194
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8200 -> false in
=======
                             FStar_Syntax_Syntax.tk = uu____8207;
                             FStar_Syntax_Syntax.pos = uu____8208;
                             FStar_Syntax_Syntax.vars = uu____8209;_},uu____8210,uu____8211))::uu____8212
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8218 -> false in
>>>>>>> origin/master
                    if Prims.op_Negation should_reify
                    then
                      let t3 = norm cfg env [] t2 in
                      let stack2 =
                        (Steps
                           ((cfg.steps), (cfg.primitive_steps),
                             (cfg.delta_level)))
                        :: stack1 in
                      let cfg1 =
<<<<<<< HEAD
                        let uu____8207 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8207
                        then
                          let uu___171_8208 = cfg in
=======
                        let uu____8225 =
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains
                               PureSubtermsWithinComputations) in
                        if uu____8225
                        then
                          let uu___169_8226 = cfg in
>>>>>>> origin/master
                          {
                            steps =
                              [PureSubtermsWithinComputations;
                              Primops;
                              AllowUnboundUniverses;
                              EraseUniverses;
                              Exclude Zeta;
                              NoDeltaSteps];
<<<<<<< HEAD
                            tcenv = (uu___171_8208.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___171_8208.primitive_steps)
                          }
                        else
                          (let uu___172_8210 = cfg in
=======
                            tcenv = (uu___169_8226.tcenv);
                            delta_level =
                              [FStar_TypeChecker_Env.Inlining;
                              FStar_TypeChecker_Env.Eager_unfolding_only];
                            primitive_steps = (uu___169_8226.primitive_steps)
                          }
                        else
                          (let uu___170_8228 = cfg in
>>>>>>> origin/master
                           {
                             steps =
                               (FStar_List.append
                                  [NoDeltaSteps; Exclude Zeta] cfg.steps);
<<<<<<< HEAD
                             tcenv = (uu___172_8210.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___172_8210.primitive_steps)
=======
                             tcenv = (uu___170_8228.tcenv);
                             delta_level = [FStar_TypeChecker_Env.NoDelta];
                             primitive_steps =
                               (uu___170_8228.primitive_steps)
>>>>>>> origin/master
                           }) in
                      norm cfg1 env
                        ((Meta
                            ((FStar_Syntax_Syntax.Meta_monadic (m1, t3)),
                              (t3.FStar_Syntax_Syntax.pos))) :: stack2) head1
                    else
<<<<<<< HEAD
                      (let uu____8212 =
                         let uu____8213 = FStar_Syntax_Subst.compress head1 in
                         uu____8213.FStar_Syntax_Syntax.n in
                       match uu____8212 with
=======
                      (let uu____8230 =
                         let uu____8231 = FStar_Syntax_Subst.compress head1 in
                         uu____8231.FStar_Syntax_Syntax.n in
                       match uu____8230 with
>>>>>>> origin/master
                       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
<<<<<<< HEAD
                           let uu____8227 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8227 with
                            | (uu____8228,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8232 ->
=======
                           let uu____8245 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8245 with
                            | (uu____8246,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____8250 ->
>>>>>>> origin/master
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
<<<<<<< HEAD
                                       let uu____8239 =
                                         let uu____8240 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8240.FStar_Syntax_Syntax.n in
                                       match uu____8239 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8245,uu____8246))
                                           ->
                                           let uu____8255 =
                                             let uu____8256 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8256.FStar_Syntax_Syntax.n in
                                           (match uu____8255 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8261,msrc,uu____8263))
=======
                                       let uu____8257 =
                                         let uu____8258 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____8258.FStar_Syntax_Syntax.n in
                                       match uu____8257 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____8263,uu____8264))
                                           ->
                                           let uu____8273 =
                                             let uu____8274 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____8274.FStar_Syntax_Syntax.n in
                                           (match uu____8273 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____8279,msrc,uu____8281))
>>>>>>> origin/master
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
<<<<<<< HEAD
                                                let uu____8272 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8272
                                            | uu____8273 -> None)
                                       | uu____8274 -> None in
                                     let uu____8275 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8275 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___173_8279 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___173_8279.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___173_8279.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___173_8279.FStar_Syntax_Syntax.lbtyp);
=======
                                                let uu____8290 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                Some uu____8290
                                            | uu____8291 -> None)
                                       | uu____8292 -> None in
                                     let uu____8293 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____8293 with
                                      | Some e ->
                                          let lb1 =
                                            let uu___171_8297 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___171_8297.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___171_8297.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___171_8297.FStar_Syntax_Syntax.lbtyp);
>>>>>>> origin/master
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Syntax_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e
                                            } in
<<<<<<< HEAD
                                          let uu____8280 =
                                            FStar_List.tl stack1 in
                                          let uu____8281 =
                                            let uu____8282 =
                                              let uu____8285 =
                                                let uu____8286 =
                                                  let uu____8294 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8294) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8286 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8285 in
                                            uu____8282 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8280 uu____8281
                                      | None  ->
                                          let uu____8311 =
                                            let uu____8312 = is_return body in
                                            match uu____8312 with
=======
                                          let uu____8298 =
                                            FStar_List.tl stack1 in
                                          let uu____8299 =
                                            let uu____8300 =
                                              let uu____8303 =
                                                let uu____8304 =
                                                  let uu____8312 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body in
                                                  ((false, [lb1]),
                                                    uu____8312) in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____8304 in
                                              FStar_Syntax_Syntax.mk
                                                uu____8303 in
                                            uu____8300 None
                                              head1.FStar_Syntax_Syntax.pos in
                                          norm cfg env uu____8298 uu____8299
                                      | None  ->
                                          let uu____8329 =
                                            let uu____8330 = is_return body in
                                            match uu____8330 with
>>>>>>> origin/master
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.tk =
<<<<<<< HEAD
                                                    uu____8315;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8316;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8317;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8322 -> false in
                                          if uu____8311
=======
                                                    uu____8333;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8334;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8335;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____8340 -> false in
                                          if uu____8329
>>>>>>> origin/master
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
<<<<<<< HEAD
                                               let uu____8342 =
                                                 let uu____8345 =
                                                   let uu____8346 =
                                                     let uu____8361 =
                                                       let uu____8363 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8363] in
                                                     (uu____8361, body1,
=======
                                               let uu____8360 =
                                                 let uu____8363 =
                                                   let uu____8364 =
                                                     let uu____8379 =
                                                       let uu____8381 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____8381] in
                                                     (uu____8379, body1,
>>>>>>> origin/master
                                                       (Some
                                                          (FStar_Util.Inr
                                                             (m1, [])))) in
                                                   FStar_Syntax_Syntax.Tm_abs
<<<<<<< HEAD
                                                     uu____8346 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8345 in
                                               uu____8342 None
=======
                                                     uu____8364 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8363 in
                                               uu____8360 None
>>>>>>> origin/master
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close1 =
                                               closure_as_term cfg env in
                                             let bind_inst =
<<<<<<< HEAD
                                               let uu____8396 =
                                                 let uu____8397 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8397.FStar_Syntax_Syntax.n in
                                               match uu____8396 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8403::uu____8404::[])
                                                   ->
                                                   let uu____8410 =
                                                     let uu____8413 =
                                                       let uu____8414 =
                                                         let uu____8419 =
                                                           let uu____8421 =
                                                             let uu____8422 =
=======
                                               let uu____8414 =
                                                 let uu____8415 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____8415.FStar_Syntax_Syntax.n in
                                               match uu____8414 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind1,uu____8421::uu____8422::[])
                                                   ->
                                                   let uu____8428 =
                                                     let uu____8431 =
                                                       let uu____8432 =
                                                         let uu____8437 =
                                                           let uu____8439 =
                                                             let uu____8440 =
>>>>>>> origin/master
                                                               close1
                                                                 lb.FStar_Syntax_Syntax.lbtyp in
                                                             (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.tcenv
<<<<<<< HEAD
                                                               uu____8422 in
                                                           let uu____8423 =
                                                             let uu____8425 =
                                                               let uu____8426
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8426 in
                                                             [uu____8425] in
                                                           uu____8421 ::
                                                             uu____8423 in
                                                         (bind1, uu____8419) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8414 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8413 in
                                                   uu____8410 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8438 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8444 =
                                                 let uu____8447 =
                                                   let uu____8448 =
                                                     let uu____8458 =
                                                       let uu____8460 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8461 =
                                                         let uu____8463 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8464 =
                                                           let uu____8466 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8467 =
                                                             let uu____8469 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8470 =
                                                               let uu____8472
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8473
                                                                 =
                                                                 let uu____8475
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8475] in
                                                               uu____8472 ::
                                                                 uu____8473 in
                                                             uu____8469 ::
                                                               uu____8470 in
                                                           uu____8466 ::
                                                             uu____8467 in
                                                         uu____8463 ::
                                                           uu____8464 in
                                                       uu____8460 ::
                                                         uu____8461 in
                                                     (bind_inst, uu____8458) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8448 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8447 in
                                               uu____8444 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8487 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8487 reified))))
=======
                                                               uu____8440 in
                                                           let uu____8441 =
                                                             let uu____8443 =
                                                               let uu____8444
                                                                 = close1 t2 in
                                                               (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.tcenv
                                                                 uu____8444 in
                                                             [uu____8443] in
                                                           uu____8439 ::
                                                             uu____8441 in
                                                         (bind1, uu____8437) in
                                                       FStar_Syntax_Syntax.Tm_uinst
                                                         uu____8432 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8431 in
                                                   uu____8428 None
                                                     t2.FStar_Syntax_Syntax.pos
                                               | uu____8456 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let reified =
                                               let uu____8462 =
                                                 let uu____8465 =
                                                   let uu____8466 =
                                                     let uu____8476 =
                                                       let uu____8478 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       let uu____8479 =
                                                         let uu____8481 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t2 in
                                                         let uu____8482 =
                                                           let uu____8484 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               FStar_Syntax_Syntax.tun in
                                                           let uu____8485 =
                                                             let uu____8487 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2 in
                                                             let uu____8488 =
                                                               let uu____8490
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   FStar_Syntax_Syntax.tun in
                                                               let uu____8491
                                                                 =
                                                                 let uu____8493
                                                                   =
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    body2 in
                                                                 [uu____8493] in
                                                               uu____8490 ::
                                                                 uu____8491 in
                                                             uu____8487 ::
                                                               uu____8488 in
                                                           uu____8484 ::
                                                             uu____8485 in
                                                         uu____8481 ::
                                                           uu____8482 in
                                                       uu____8478 ::
                                                         uu____8479 in
                                                     (bind_inst, uu____8476) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8466 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8465 in
                                               uu____8462 None
                                                 t2.FStar_Syntax_Syntax.pos in
                                             let uu____8505 =
                                               FStar_List.tl stack1 in
                                             norm cfg env uu____8505 reified))))
>>>>>>> origin/master
                       | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                           let ed =
                             FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                               m1 in
<<<<<<< HEAD
                           let uu____8505 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8505 with
                            | (uu____8506,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8529 =
                                        let uu____8530 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8530.FStar_Syntax_Syntax.n in
                                      match uu____8529 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8536) -> t4
                                      | uu____8541 -> head2 in
                                    let uu____8542 =
                                      let uu____8543 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8543.FStar_Syntax_Syntax.n in
                                    match uu____8542 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8548 -> None in
                                  let uu____8549 = maybe_extract_fv head2 in
                                  match uu____8549 with
                                  | Some x when
                                      let uu____8555 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8555
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8559 =
                                          maybe_extract_fv head3 in
                                        match uu____8559 with
                                        | Some uu____8562 -> Some true
                                        | uu____8563 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8566 -> (head2, None) in
                                ((let is_arg_impure uu____8577 =
                                    match uu____8577 with
                                    | (e,q) ->
                                        let uu____8582 =
                                          let uu____8583 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8583.FStar_Syntax_Syntax.n in
                                        (match uu____8582 with
=======
                           let uu____8523 = ed.FStar_Syntax_Syntax.bind_repr in
                           (match uu____8523 with
                            | (uu____8524,bind_repr) ->
                                let maybe_unfold_action head2 =
                                  let maybe_extract_fv t3 =
                                    let t4 =
                                      let uu____8547 =
                                        let uu____8548 =
                                          FStar_Syntax_Subst.compress t3 in
                                        uu____8548.FStar_Syntax_Syntax.n in
                                      match uu____8547 with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          (t4,uu____8554) -> t4
                                      | uu____8559 -> head2 in
                                    let uu____8560 =
                                      let uu____8561 =
                                        FStar_Syntax_Subst.compress t4 in
                                      uu____8561.FStar_Syntax_Syntax.n in
                                    match uu____8560 with
                                    | FStar_Syntax_Syntax.Tm_fvar x -> Some x
                                    | uu____8566 -> None in
                                  let uu____8567 = maybe_extract_fv head2 in
                                  match uu____8567 with
                                  | Some x when
                                      let uu____8573 =
                                        FStar_Syntax_Syntax.lid_of_fv x in
                                      FStar_TypeChecker_Env.is_action
                                        cfg.tcenv uu____8573
                                      ->
                                      let head3 = norm cfg env [] head2 in
                                      let action_unfolded =
                                        let uu____8577 =
                                          maybe_extract_fv head3 in
                                        match uu____8577 with
                                        | Some uu____8580 -> Some true
                                        | uu____8581 -> Some false in
                                      (head3, action_unfolded)
                                  | uu____8584 -> (head2, None) in
                                ((let is_arg_impure uu____8595 =
                                    match uu____8595 with
                                    | (e,q) ->
                                        let uu____8600 =
                                          let uu____8601 =
                                            FStar_Syntax_Subst.compress e in
                                          uu____8601.FStar_Syntax_Syntax.n in
                                        (match uu____8600 with
>>>>>>> origin/master
                                         | FStar_Syntax_Syntax.Tm_meta
                                             (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                              (m11,m2,t'))
                                             ->
                                             Prims.op_Negation
                                               (FStar_Syntax_Util.is_pure_effect
                                                  m11)
<<<<<<< HEAD
                                         | uu____8598 -> false) in
                                  let uu____8599 =
                                    let uu____8600 =
                                      let uu____8604 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8604 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8600 in
                                  if uu____8599
                                  then
                                    let uu____8607 =
                                      let uu____8608 =
=======
                                         | uu____8616 -> false) in
                                  let uu____8617 =
                                    let uu____8618 =
                                      let uu____8622 =
                                        FStar_Syntax_Syntax.as_arg head_app in
                                      uu____8622 :: args in
                                    FStar_Util.for_some is_arg_impure
                                      uu____8618 in
                                  if uu____8617
                                  then
                                    let uu____8625 =
                                      let uu____8626 =
>>>>>>> origin/master
                                        FStar_Syntax_Print.term_to_string
                                          head1 in
                                      FStar_Util.format1
                                        "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
<<<<<<< HEAD
                                        uu____8608 in
                                    failwith uu____8607
                                  else ());
                                 (let uu____8610 =
                                    maybe_unfold_action head_app in
                                  match uu____8610 with
=======
                                        uu____8626 in
                                    failwith uu____8625
                                  else ());
                                 (let uu____8628 =
                                    maybe_unfold_action head_app in
                                  match uu____8628 with
>>>>>>> origin/master
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
<<<<<<< HEAD
                                      let uu____8645 = FStar_List.tl stack1 in
                                      norm cfg env uu____8645 body1)))
=======
                                      let uu____8663 = FStar_List.tl stack1 in
                                      norm cfg env uu____8663 body1)))
>>>>>>> origin/master
                       | FStar_Syntax_Syntax.Tm_meta
                           (e,FStar_Syntax_Syntax.Meta_monadic_lift
                            (msrc,mtgt,t'))
                           ->
                           let lifted =
<<<<<<< HEAD
                             let uu____8659 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8659 in
                           let uu____8660 = FStar_List.tl stack1 in
                           norm cfg env uu____8660 lifted
=======
                             let uu____8677 = closure_as_term cfg env t' in
                             reify_lift cfg.tcenv e msrc mtgt uu____8677 in
                           let uu____8678 = FStar_List.tl stack1 in
                           norm cfg env uu____8678 lifted
>>>>>>> origin/master
                       | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                           let branches1 =
                             FStar_All.pipe_right branches
                               (FStar_List.map
<<<<<<< HEAD
                                  (fun uu____8743  ->
                                     match uu____8743 with
                                     | (pat,wopt,tm) ->
                                         let uu____8781 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8781))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8807 = FStar_List.tl stack1 in
                           norm cfg env uu____8807 tm
                       | uu____8808 -> norm cfg env stack1 head1)
=======
                                  (fun uu____8761  ->
                                     match uu____8761 with
                                     | (pat,wopt,tm) ->
                                         let uu____8799 =
                                           FStar_Syntax_Util.mk_reify tm in
                                         (pat, wopt, uu____8799))) in
                           let tm =
                             mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                               t2.FStar_Syntax_Syntax.pos in
                           let uu____8825 = FStar_List.tl stack1 in
                           norm cfg env uu____8825 tm
                       | uu____8826 -> norm cfg env stack1 head1)
>>>>>>> origin/master
                | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                    let should_reify =
                      match stack1 with
                      | (App
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reify );
<<<<<<< HEAD
                             FStar_Syntax_Syntax.tk = uu____8817;
                             FStar_Syntax_Syntax.pos = uu____8818;
                             FStar_Syntax_Syntax.vars = uu____8819;_},uu____8820,uu____8821))::uu____8822
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8828 -> false in
                    if should_reify
                    then
                      let uu____8829 = FStar_List.tl stack1 in
                      let uu____8830 =
                        let uu____8831 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8831 in
                      norm cfg env uu____8829 uu____8830
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8834 =
=======
                             FStar_Syntax_Syntax.tk = uu____8835;
                             FStar_Syntax_Syntax.pos = uu____8836;
                             FStar_Syntax_Syntax.vars = uu____8837;_},uu____8838,uu____8839))::uu____8840
                          ->
                          FStar_All.pipe_right cfg.steps
                            (FStar_List.contains Reify)
                      | uu____8846 -> false in
                    if should_reify
                    then
                      let uu____8847 = FStar_List.tl stack1 in
                      let uu____8848 =
                        let uu____8849 = closure_as_term cfg env t2 in
                        reify_lift cfg.tcenv head1 m1 m' uu____8849 in
                      norm cfg env uu____8847 uu____8848
                    else
                      (let t3 = norm cfg env [] t2 in
                       let uu____8852 =
>>>>>>> origin/master
                         ((FStar_Syntax_Util.is_pure_effect m1) ||
                            (FStar_Syntax_Util.is_ghost_effect m1))
                           &&
                           (FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations)) in
<<<<<<< HEAD
                       if uu____8834
=======
                       if uu____8852
>>>>>>> origin/master
                       then
                         let stack2 =
                           (Steps
                              ((cfg.steps), (cfg.primitive_steps),
                                (cfg.delta_level)))
                           :: stack1 in
                         let cfg1 =
<<<<<<< HEAD
                           let uu___174_8840 = cfg in
=======
                           let uu___172_8858 = cfg in
>>>>>>> origin/master
                           {
                             steps =
                               [PureSubtermsWithinComputations;
                               Primops;
                               AllowUnboundUniverses;
                               EraseUniverses;
                               Exclude Zeta];
<<<<<<< HEAD
                             tcenv = (uu___174_8840.tcenv);
=======
                             tcenv = (uu___172_8858.tcenv);
>>>>>>> origin/master
                             delta_level =
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Eager_unfolding_only];
                             primitive_steps =
<<<<<<< HEAD
                               (uu___174_8840.primitive_steps)
=======
                               (uu___172_8858.primitive_steps)
>>>>>>> origin/master
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
<<<<<<< HEAD
                | uu____8842 ->
                    (match stack1 with
                     | uu____8843::uu____8844 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8848)
=======
                | uu____8860 ->
                    (match stack1 with
                     | uu____8861::uu____8862 ->
                         (match m with
                          | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____8866)
>>>>>>> origin/master
                              -> norm cfg env ((Meta (m, r)) :: stack1) head1
                          | FStar_Syntax_Syntax.Meta_pattern args ->
                              let args1 = norm_pattern_args cfg env args in
                              norm cfg env
                                ((Meta
                                    ((FStar_Syntax_Syntax.Meta_pattern args1),
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) head1
<<<<<<< HEAD
                          | uu____8863 -> norm cfg env stack1 head1)
=======
                          | uu____8881 -> norm cfg env stack1 head1)
>>>>>>> origin/master
                     | [] ->
                         let head2 = norm cfg env [] head1 in
                         let m1 =
                           match m with
                           | FStar_Syntax_Syntax.Meta_pattern args ->
<<<<<<< HEAD
                               let uu____8873 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8873
                           | uu____8880 -> m in
=======
                               let uu____8891 =
                                 norm_pattern_args cfg env args in
                               FStar_Syntax_Syntax.Meta_pattern uu____8891
                           | uu____8898 -> m in
>>>>>>> origin/master
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
<<<<<<< HEAD
              let uu____8892 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8892 with
              | (uu____8893,return_repr) ->
                  let return_inst =
                    let uu____8900 =
                      let uu____8901 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8901.FStar_Syntax_Syntax.n in
                    match uu____8900 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8907::[])
                        ->
                        let uu____8913 =
                          let uu____8916 =
                            let uu____8917 =
                              let uu____8922 =
                                let uu____8924 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8924] in
                              (return_tm, uu____8922) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8917 in
                          FStar_Syntax_Syntax.mk uu____8916 in
                        uu____8913 None e.FStar_Syntax_Syntax.pos
                    | uu____8936 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8939 =
                    let uu____8942 =
                      let uu____8943 =
                        let uu____8953 =
                          let uu____8955 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8956 =
                            let uu____8958 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8958] in
                          uu____8955 :: uu____8956 in
                        (return_inst, uu____8953) in
                      FStar_Syntax_Syntax.Tm_app uu____8943 in
                    FStar_Syntax_Syntax.mk uu____8942 in
                  uu____8939 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8971 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8971 with
               | None  ->
                   let uu____8973 =
=======
              let uu____8910 = ed.FStar_Syntax_Syntax.return_repr in
              match uu____8910 with
              | (uu____8911,return_repr) ->
                  let return_inst =
                    let uu____8918 =
                      let uu____8919 =
                        FStar_Syntax_Subst.compress return_repr in
                      uu____8919.FStar_Syntax_Syntax.n in
                    match uu____8918 with
                    | FStar_Syntax_Syntax.Tm_uinst (return_tm,uu____8925::[])
                        ->
                        let uu____8931 =
                          let uu____8934 =
                            let uu____8935 =
                              let uu____8940 =
                                let uu____8942 =
                                  env.FStar_TypeChecker_Env.universe_of env t in
                                [uu____8942] in
                              (return_tm, uu____8940) in
                            FStar_Syntax_Syntax.Tm_uinst uu____8935 in
                          FStar_Syntax_Syntax.mk uu____8934 in
                        uu____8931 None e.FStar_Syntax_Syntax.pos
                    | uu____8954 ->
                        failwith "NIY : Reification of indexed effects" in
                  let uu____8957 =
                    let uu____8960 =
                      let uu____8961 =
                        let uu____8971 =
                          let uu____8973 = FStar_Syntax_Syntax.as_arg t in
                          let uu____8974 =
                            let uu____8976 = FStar_Syntax_Syntax.as_arg e in
                            [uu____8976] in
                          uu____8973 :: uu____8974 in
                        (return_inst, uu____8971) in
                      FStar_Syntax_Syntax.Tm_app uu____8961 in
                    FStar_Syntax_Syntax.mk uu____8960 in
                  uu____8957 None e.FStar_Syntax_Syntax.pos
            else
              (let uu____8989 = FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____8989 with
               | None  ->
                   let uu____8991 =
>>>>>>> origin/master
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
<<<<<<< HEAD
                   failwith uu____8973
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8974;
                     FStar_TypeChecker_Env.mtarget = uu____8975;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8976;
=======
                   failwith uu____8991
               | Some
                   { FStar_TypeChecker_Env.msource = uu____8992;
                     FStar_TypeChecker_Env.mtarget = uu____8993;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8994;
>>>>>>> origin/master
                         FStar_TypeChecker_Env.mlift_term = None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | Some
<<<<<<< HEAD
                   { FStar_TypeChecker_Env.msource = uu____8987;
                     FStar_TypeChecker_Env.mtarget = uu____8988;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____8989;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9007 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9007)
=======
                   { FStar_TypeChecker_Env.msource = uu____9005;
                     FStar_TypeChecker_Env.mtarget = uu____9006;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____9007;
                         FStar_TypeChecker_Env.mlift_term = Some lift;_};_}
                   ->
                   let uu____9025 = FStar_Syntax_Util.mk_reify e in
                   lift t FStar_Syntax_Syntax.tun uu____9025)
>>>>>>> origin/master
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
<<<<<<< HEAD
                (fun uu____9037  ->
                   match uu____9037 with
                   | (a,imp) ->
                       let uu____9044 = norm cfg env [] a in
                       (uu____9044, imp))))
=======
                (fun uu____9055  ->
                   match uu____9055 with
                   | (a,imp) ->
                       let uu____9062 = norm cfg env [] a in
                       (uu____9062, imp))))
>>>>>>> origin/master
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        let comp1 = ghost_to_pure_aux cfg env comp in
        match comp1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
<<<<<<< HEAD
            let uu___175_9059 = comp1 in
            let uu____9062 =
              let uu____9063 =
                let uu____9069 = norm cfg env [] t in
                let uu____9070 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9069, uu____9070) in
              FStar_Syntax_Syntax.Total uu____9063 in
            {
              FStar_Syntax_Syntax.n = uu____9062;
              FStar_Syntax_Syntax.tk = (uu___175_9059.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_9059.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_9059.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___176_9085 = comp1 in
            let uu____9088 =
              let uu____9089 =
                let uu____9095 = norm cfg env [] t in
                let uu____9096 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9095, uu____9096) in
              FStar_Syntax_Syntax.GTotal uu____9089 in
            {
              FStar_Syntax_Syntax.n = uu____9088;
              FStar_Syntax_Syntax.tk = (uu___176_9085.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___176_9085.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___176_9085.FStar_Syntax_Syntax.vars)
=======
            let uu___173_9077 = comp1 in
            let uu____9080 =
              let uu____9081 =
                let uu____9087 = norm cfg env [] t in
                let uu____9088 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9087, uu____9088) in
              FStar_Syntax_Syntax.Total uu____9081 in
            {
              FStar_Syntax_Syntax.n = uu____9080;
              FStar_Syntax_Syntax.tk = (uu___173_9077.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___173_9077.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___173_9077.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___174_9103 = comp1 in
            let uu____9106 =
              let uu____9107 =
                let uu____9113 = norm cfg env [] t in
                let uu____9114 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____9113, uu____9114) in
              FStar_Syntax_Syntax.GTotal uu____9107 in
            {
              FStar_Syntax_Syntax.n = uu____9106;
              FStar_Syntax_Syntax.tk = (uu___174_9103.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___174_9103.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___174_9103.FStar_Syntax_Syntax.vars)
>>>>>>> origin/master
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
<<<<<<< HEAD
                   (fun uu____9127  ->
                      match uu____9127 with
                      | (a,i) ->
                          let uu____9134 = norm cfg env [] a in
                          (uu____9134, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___139_9139  ->
                      match uu___139_9139 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9143 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9143
                      | f -> f)) in
            let uu___177_9147 = comp1 in
            let uu____9150 =
              let uu____9151 =
                let uu___178_9152 = ct in
                let uu____9153 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9154 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9157 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9153;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___178_9152.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9154;
                  FStar_Syntax_Syntax.effect_args = uu____9157;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9151 in
            {
              FStar_Syntax_Syntax.n = uu____9150;
              FStar_Syntax_Syntax.tk = (uu___177_9147.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___177_9147.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___177_9147.FStar_Syntax_Syntax.vars)
=======
                   (fun uu____9145  ->
                      match uu____9145 with
                      | (a,i) ->
                          let uu____9152 = norm cfg env [] a in
                          (uu____9152, i))) in
            let flags =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___138_9157  ->
                      match uu___138_9157 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____9161 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____9161
                      | f -> f)) in
            let uu___175_9165 = comp1 in
            let uu____9168 =
              let uu____9169 =
                let uu___176_9170 = ct in
                let uu____9171 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____9172 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____9175 = norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____9171;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___176_9170.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____9172;
                  FStar_Syntax_Syntax.effect_args = uu____9175;
                  FStar_Syntax_Syntax.flags = flags
                } in
              FStar_Syntax_Syntax.Comp uu____9169 in
            {
              FStar_Syntax_Syntax.n = uu____9168;
              FStar_Syntax_Syntax.tk = (uu___175_9165.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___175_9165.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___175_9165.FStar_Syntax_Syntax.vars)
>>>>>>> origin/master
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
<<<<<<< HEAD
            (let uu___179_9174 = cfg in
=======
            (let uu___177_9192 = cfg in
>>>>>>> origin/master
             {
               steps =
                 [Eager_unfolding;
                 UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
                 AllowUnboundUniverses];
<<<<<<< HEAD
               tcenv = (uu___179_9174.tcenv);
               delta_level = (uu___179_9174.delta_level);
               primitive_steps = (uu___179_9174.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9179 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9179 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9182 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___180_9196 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___180_9196.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___180_9196.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___180_9196.FStar_Syntax_Syntax.vars)
=======
               tcenv = (uu___177_9192.tcenv);
               delta_level = (uu___177_9192.delta_level);
               primitive_steps = (uu___177_9192.primitive_steps)
             }) env [] t in
        let non_info t =
          let uu____9197 = norm1 t in
          FStar_Syntax_Util.non_informative uu____9197 in
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____9200 -> c
        | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
            let uu___178_9214 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
              FStar_Syntax_Syntax.tk = (uu___178_9214.FStar_Syntax_Syntax.tk);
              FStar_Syntax_Syntax.pos =
                (uu___178_9214.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___178_9214.FStar_Syntax_Syntax.vars)
>>>>>>> origin/master
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                ct.FStar_Syntax_Syntax.effect_name in
<<<<<<< HEAD
            let uu____9206 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9206
=======
            let uu____9224 =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (non_info ct.FStar_Syntax_Syntax.result_typ) in
            if uu____9224
>>>>>>> origin/master
            then
              let ct1 =
                match downgrade_ghost_effect_name
                        ct.FStar_Syntax_Syntax.effect_name
                with
                | Some pure_eff ->
<<<<<<< HEAD
                    let uu___181_9211 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___181_9211.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___181_9211.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___181_9211.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___181_9211.FStar_Syntax_Syntax.flags)
=======
                    let uu___179_9229 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___179_9229.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___179_9229.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___179_9229.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___179_9229.FStar_Syntax_Syntax.flags)
>>>>>>> origin/master
                    }
                | None  ->
                    let ct1 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
<<<<<<< HEAD
                    let uu___182_9213 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___182_9213.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___182_9213.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___182_9213.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___182_9213.FStar_Syntax_Syntax.flags)
                    } in
              let uu___183_9214 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___183_9214.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___183_9214.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___183_9214.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9220 -> c
=======
                    let uu___180_9231 = ct1 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___180_9231.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Syntax_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___180_9231.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___180_9231.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___180_9231.FStar_Syntax_Syntax.flags)
                    } in
              let uu___181_9232 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.tk =
                  (uu___181_9232.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___181_9232.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___181_9232.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu____9238 -> c
>>>>>>> origin/master
and norm_binder:
  cfg ->
    env ->
      FStar_Syntax_Syntax.binder ->
        (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun cfg  ->
    fun env  ->
<<<<<<< HEAD
      fun uu____9223  ->
        match uu____9223 with
        | (x,imp) ->
            let uu____9226 =
              let uu___184_9227 = x in
              let uu____9228 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___184_9227.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___184_9227.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9228
              } in
            (uu____9226, imp)
=======
      fun uu____9241  ->
        match uu____9241 with
        | (x,imp) ->
            let uu____9244 =
              let uu___182_9245 = x in
              let uu____9246 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___182_9245.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___182_9245.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____9246
              } in
            (uu____9244, imp)
>>>>>>> origin/master
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
<<<<<<< HEAD
        let uu____9234 =
          FStar_List.fold_left
            (fun uu____9241  ->
               fun b  ->
                 match uu____9241 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9234 with | (nbs,uu____9258) -> FStar_List.rev nbs
=======
        let uu____9252 =
          FStar_List.fold_left
            (fun uu____9259  ->
               fun b  ->
                 match uu____9259 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (Dummy :: env1))) ([], env) bs in
        match uu____9252 with | (nbs,uu____9276) -> FStar_List.rev nbs
>>>>>>> origin/master
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
<<<<<<< HEAD
            let uu____9275 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9275
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9280 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9280
               then
                 let uu____9284 =
                   let uu____9287 =
                     let uu____9288 =
                       let uu____9291 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9291 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9288 in
                   FStar_Util.Inl uu____9287 in
                 Some uu____9284
               else
                 (let uu____9295 =
                    let uu____9298 =
                      let uu____9299 =
                        let uu____9302 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9302 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9299 in
                    FStar_Util.Inl uu____9298 in
                  Some uu____9295))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9315 -> lopt
=======
            let uu____9293 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
            if uu____9293
            then
              let t = norm cfg env [] lc.FStar_Syntax_Syntax.res_typ in
              let uu____9298 = FStar_Syntax_Util.is_total_lcomp lc in
              (if uu____9298
               then
                 let uu____9302 =
                   let uu____9305 =
                     let uu____9306 =
                       let uu____9309 = FStar_Syntax_Syntax.mk_Total t in
                       FStar_Syntax_Util.comp_set_flags uu____9309 flags in
                     FStar_Syntax_Util.lcomp_of_comp uu____9306 in
                   FStar_Util.Inl uu____9305 in
                 Some uu____9302
               else
                 (let uu____9313 =
                    let uu____9316 =
                      let uu____9317 =
                        let uu____9320 = FStar_Syntax_Syntax.mk_GTotal t in
                        FStar_Syntax_Util.comp_set_flags uu____9320 flags in
                      FStar_Syntax_Util.lcomp_of_comp uu____9317 in
                    FStar_Util.Inl uu____9316 in
                  Some uu____9313))
            else
              Some
                (FStar_Util.Inr ((lc.FStar_Syntax_Syntax.eff_name), flags))
        | uu____9333 -> lopt
>>>>>>> origin/master
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
<<<<<<< HEAD
              ((let uu____9327 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9327
                then
                  let uu____9328 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9329 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9328
                    uu____9329
=======
              ((let uu____9345 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
                    (FStar_Options.Other "print_normalized_terms") in
                if uu____9345
                then
                  let uu____9346 = FStar_Syntax_Print.term_to_string tm in
                  let uu____9347 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2 "Normalized %s to %s\n" uu____9346
                    uu____9347
>>>>>>> origin/master
                else ());
               rebuild cfg env stack2 t)
          | (Steps (s,ps,dl))::stack2 ->
              rebuild
<<<<<<< HEAD
                (let uu___185_9340 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___185_9340.tcenv);
=======
                (let uu___183_9358 = cfg in
                 {
                   steps = s;
                   tcenv = (uu___183_9358.tcenv);
>>>>>>> origin/master
                   delta_level = dl;
                   primitive_steps = ps
                 }) env stack2 t
          | (Meta (m,r))::stack2 ->
              let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
              rebuild cfg env stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo r (env, t);
               log cfg
<<<<<<< HEAD
                 (fun uu____9360  ->
                    let uu____9361 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9361);
=======
                 (fun uu____9378  ->
                    let uu____9379 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "\tSet memo %s\n" uu____9379);
>>>>>>> origin/master
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
<<<<<<< HEAD
              let uu____9398 =
                let uu___186_9399 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___186_9399.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___186_9399.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___186_9399.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9398
          | (Arg (Univ uu____9404,uu____9405,uu____9406))::uu____9407 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9409,uu____9410))::uu____9411 ->
=======
              let uu____9416 =
                let uu___184_9417 = FStar_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___184_9417.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___184_9417.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___184_9417.FStar_Syntax_Syntax.vars)
                } in
              rebuild cfg env stack2 uu____9416
          | (Arg (Univ uu____9422,uu____9423,uu____9424))::uu____9425 ->
              failwith "Impossible"
          | (Arg (Dummy ,uu____9427,uu____9428))::uu____9429 ->
>>>>>>> origin/master
              failwith "Impossible"
          | (UnivArgs (us,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env stack2 t1
<<<<<<< HEAD
          | (Arg (Clos (env1,tm,m,uu____9423),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9439  ->
                    let uu____9440 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9440);
=======
          | (Arg (Clos (env1,tm,m,uu____9441),aq,r))::stack2 ->
              (log cfg
                 (fun uu____9457  ->
                    let uu____9458 = FStar_Syntax_Print.term_to_string tm in
                    FStar_Util.print1 "Rebuilding with arg %s\n" uu____9458);
>>>>>>> origin/master
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
<<<<<<< HEAD
                 (let uu____9451 = FStar_ST.read m in
                  match uu____9451 with
=======
                 (let uu____9469 = FStar_ST.read m in
                  match uu____9469 with
>>>>>>> origin/master
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
<<<<<<< HEAD
                  | Some (uu____9477,a) ->
=======
                  | Some (uu____9495,a) ->
>>>>>>> origin/master
                      let t1 =
                        FStar_Syntax_Syntax.extend_app t (a, aq) None r in
                      rebuild cfg env1 stack2 t1))
          | (App (head1,aq,r))::stack2 ->
              let t1 = FStar_Syntax_Syntax.extend_app head1 (t, aq) None r in
<<<<<<< HEAD
              let uu____9499 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9499
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9506  ->
                    let uu____9507 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9507);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9512 =
                  log cfg
                    (fun uu____9514  ->
                       let uu____9515 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9516 =
                         let uu____9517 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9524  ->
                                   match uu____9524 with
                                   | (p,uu____9530,uu____9531) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9517
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9515 uu____9516);
=======
              let uu____9517 = maybe_simplify cfg t1 in
              rebuild cfg env stack2 uu____9517
          | (Match (env1,branches,r))::stack2 ->
              (log cfg
                 (fun uu____9524  ->
                    let uu____9525 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n"
                      uu____9525);
               (let scrutinee = t in
                let norm_and_rebuild_match uu____9530 =
                  log cfg
                    (fun uu____9532  ->
                       let uu____9533 =
                         FStar_Syntax_Print.term_to_string scrutinee in
                       let uu____9534 =
                         let uu____9535 =
                           FStar_All.pipe_right branches
                             (FStar_List.map
                                (fun uu____9542  ->
                                   match uu____9542 with
                                   | (p,uu____9548,uu____9549) ->
                                       FStar_Syntax_Print.pat_to_string p)) in
                         FStar_All.pipe_right uu____9535
                           (FStar_String.concat "\n\t") in
                       FStar_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu____9533 uu____9534);
>>>>>>> origin/master
                  (let whnf = FStar_List.contains WHNF cfg.steps in
                   let cfg_exclude_iota_zeta =
                     let new_delta =
                       FStar_All.pipe_right cfg.delta_level
                         (FStar_List.filter
<<<<<<< HEAD
                            (fun uu___140_9541  ->
                               match uu___140_9541 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9542 -> false)) in
                     let steps' =
                       let uu____9545 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9545
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___187_9548 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___187_9548.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___187_9548.primitive_steps)
=======
                            (fun uu___139_9559  ->
                               match uu___139_9559 with
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | uu____9560 -> false)) in
                     let steps' =
                       let uu____9563 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       if uu____9563
                       then [Exclude Zeta]
                       else [Exclude Iota; Exclude Zeta] in
                     let uu___185_9566 = cfg in
                     {
                       steps = (FStar_List.append steps' cfg.steps);
                       tcenv = (uu___185_9566.tcenv);
                       delta_level = new_delta;
                       primitive_steps = (uu___185_9566.primitive_steps)
>>>>>>> origin/master
                     } in
                   let norm_or_whnf env2 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_iota_zeta env2 t1
                     else norm cfg_exclude_iota_zeta env2 [] t1 in
                   let rec norm_pat env2 p =
                     match p.FStar_Syntax_Syntax.v with
<<<<<<< HEAD
                     | FStar_Syntax_Syntax.Pat_constant uu____9582 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9598 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9632  ->
                                   fun uu____9633  ->
                                     match (uu____9632, uu____9633) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9698 = norm_pat env3 p1 in
                                         (match uu____9698 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9598 with
                          | (pats1,env3) ->
                              ((let uu___188_9764 = p in
=======
                     | FStar_Syntax_Syntax.Pat_constant uu____9600 ->
                         (p, env2)
                     | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                         let uu____9616 =
                           FStar_All.pipe_right pats
                             (FStar_List.fold_left
                                (fun uu____9650  ->
                                   fun uu____9651  ->
                                     match (uu____9650, uu____9651) with
                                     | ((pats1,env3),(p1,b)) ->
                                         let uu____9716 = norm_pat env3 p1 in
                                         (match uu____9716 with
                                          | (p2,env4) ->
                                              (((p2, b) :: pats1), env4)))
                                ([], env2)) in
                         (match uu____9616 with
                          | (pats1,env3) ->
                              ((let uu___186_9782 = p in
>>>>>>> origin/master
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_cons
                                       (fv, (FStar_List.rev pats1)));
                                  FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                                    (uu___188_9764.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___188_9764.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___189_9778 = x in
                           let uu____9779 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_9778.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_9778.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9779
                           } in
                         ((let uu___190_9785 = p in
=======
                                    (uu___186_9782.FStar_Syntax_Syntax.ty);
                                  FStar_Syntax_Syntax.p =
                                    (uu___186_9782.FStar_Syntax_Syntax.p)
                                }), env3))
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___187_9796 = x in
                           let uu____9797 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___187_9796.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___187_9796.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9797
                           } in
                         ((let uu___188_9803 = p in
>>>>>>> origin/master
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var x1);
                             FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                               (uu___190_9785.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___190_9785.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___191_9790 = x in
                           let uu____9791 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_9790.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_9790.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9791
                           } in
                         ((let uu___192_9797 = p in
=======
                               (uu___188_9803.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___188_9803.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let x1 =
                           let uu___189_9808 = x in
                           let uu____9809 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___189_9808.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___189_9808.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9809
                           } in
                         ((let uu___190_9815 = p in
>>>>>>> origin/master
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild x1);
                             FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                               (uu___192_9797.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_9797.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___193_9807 = x in
                           let uu____9808 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___193_9807.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___193_9807.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9808
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___194_9815 = p in
=======
                               (uu___190_9815.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___190_9815.FStar_Syntax_Syntax.p)
                           }), (Dummy :: env2))
                     | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                         let x1 =
                           let uu___191_9825 = x in
                           let uu____9826 =
                             norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___191_9825.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___191_9825.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____9826
                           } in
                         let t2 = norm_or_whnf env2 t1 in
                         ((let uu___192_9833 = p in
>>>>>>> origin/master
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                             FStar_Syntax_Syntax.ty =
<<<<<<< HEAD
                               (uu___194_9815.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___194_9815.FStar_Syntax_Syntax.p)
=======
                               (uu___192_9833.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___192_9833.FStar_Syntax_Syntax.p)
>>>>>>> origin/master
                           }), env2) in
                   let branches1 =
                     match env1 with
                     | [] when whnf -> branches
<<<<<<< HEAD
                     | uu____9819 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9822 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9822 with
                                 | (p,wopt,e) ->
                                     let uu____9840 = norm_pat env1 p in
                                     (match uu____9840 with
=======
                     | uu____9837 ->
                         FStar_All.pipe_right branches
                           (FStar_List.map
                              (fun branch1  ->
                                 let uu____9840 =
                                   FStar_Syntax_Subst.open_branch branch1 in
                                 match uu____9840 with
                                 | (p,wopt,e) ->
                                     let uu____9858 = norm_pat env1 p in
                                     (match uu____9858 with
>>>>>>> origin/master
                                      | (p1,env2) ->
                                          let wopt1 =
                                            match wopt with
                                            | None  -> None
                                            | Some w ->
<<<<<<< HEAD
                                                let uu____9864 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9864 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9869 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9869) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9879) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9884 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9885;
                        FStar_Syntax_Syntax.fv_delta = uu____9886;
=======
                                                let uu____9882 =
                                                  norm_or_whnf env2 w in
                                                Some uu____9882 in
                                          let e1 = norm_or_whnf env2 e in
                                          FStar_Syntax_Util.branch
                                            (p1, wopt1, e1)))) in
                   let uu____9887 =
                     mk (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                       r in
                   rebuild cfg env1 stack2 uu____9887) in
                let rec is_cons head1 =
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_uinst (h,uu____9897) -> is_cons h
                  | FStar_Syntax_Syntax.Tm_constant uu____9902 -> true
                  | FStar_Syntax_Syntax.Tm_fvar
                      { FStar_Syntax_Syntax.fv_name = uu____9903;
                        FStar_Syntax_Syntax.fv_delta = uu____9904;
>>>>>>> origin/master
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Data_ctor );_}
                      -> true
                  | FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
                      { FStar_Syntax_Syntax.fv_name = uu____9890;
                        FStar_Syntax_Syntax.fv_delta = uu____9891;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9892);_}
                      -> true
                  | uu____9899 -> false in
=======
                      { FStar_Syntax_Syntax.fv_name = uu____9908;
                        FStar_Syntax_Syntax.fv_delta = uu____9909;
                        FStar_Syntax_Syntax.fv_qual = Some
                          (FStar_Syntax_Syntax.Record_ctor uu____9910);_}
                      -> true
                  | uu____9917 -> false in
>>>>>>> origin/master
                let guard_when_clause wopt b rest =
                  match wopt with
                  | None  -> b
                  | Some w ->
                      let then_branch = b in
                      let else_branch =
                        mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest)) r in
                      FStar_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee1 p =
                  let scrutinee2 = FStar_Syntax_Util.unmeta scrutinee1 in
<<<<<<< HEAD
                  let uu____9998 = FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____9998 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10030 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10032 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10034 ->
=======
                  let uu____10016 =
                    FStar_Syntax_Util.head_and_args scrutinee2 in
                  match uu____10016 with
                  | (head1,args) ->
                      (match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var uu____10048 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_wild uu____10050 ->
                           FStar_Util.Inl [scrutinee2]
                       | FStar_Syntax_Syntax.Pat_dot_term uu____10052 ->
>>>>>>> origin/master
                           FStar_Util.Inl []
                       | FStar_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_constant s' when 
                                s = s' -> FStar_Util.Inl []
<<<<<<< HEAD
                            | uu____10046 ->
                                let uu____10047 =
                                  let uu____10048 = is_cons head1 in
                                  Prims.op_Negation uu____10048 in
                                FStar_Util.Inr uu____10047)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10062 =
                             let uu____10063 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10063.FStar_Syntax_Syntax.n in
                           (match uu____10062 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10070 ->
                                let uu____10071 =
                                  let uu____10072 = is_cons head1 in
                                  Prims.op_Negation uu____10072 in
                                FStar_Util.Inr uu____10071))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10106)::rest_a,(p1,uu____10109)::rest_p) ->
                      let uu____10137 = matches_pat t1 p1 in
                      (match uu____10137 with
=======
                            | uu____10064 ->
                                let uu____10065 =
                                  let uu____10066 = is_cons head1 in
                                  Prims.op_Negation uu____10066 in
                                FStar_Util.Inr uu____10065)
                       | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                           let uu____10080 =
                             let uu____10081 =
                               FStar_Syntax_Util.un_uinst head1 in
                             uu____10081.FStar_Syntax_Syntax.n in
                           (match uu____10080 with
                            | FStar_Syntax_Syntax.Tm_fvar fv' when
                                FStar_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu____10088 ->
                                let uu____10089 =
                                  let uu____10090 = is_cons head1 in
                                  Prims.op_Negation uu____10090 in
                                FStar_Util.Inr uu____10089))
                and matches_args out a p =
                  match (a, p) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t1,uu____10124)::rest_a,(p1,uu____10127)::rest_p) ->
                      let uu____10155 = matches_pat t1 p1 in
                      (match uu____10155 with
>>>>>>> origin/master
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
<<<<<<< HEAD
                  | uu____10151 -> FStar_Util.Inr false in
=======
                  | uu____10169 -> FStar_Util.Inr false in
>>>>>>> origin/master
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1,wopt,b)::rest ->
<<<<<<< HEAD
                      let uu____10222 = matches_pat scrutinee1 p1 in
                      (match uu____10222 with
=======
                      let uu____10240 = matches_pat scrutinee1 p1 in
                      (match uu____10240 with
>>>>>>> origin/master
                       | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                       | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                       | FStar_Util.Inl s ->
                           (log cfg
<<<<<<< HEAD
                              (fun uu____10232  ->
                                 let uu____10233 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10234 =
                                   let uu____10235 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10235
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10233 uu____10234);
=======
                              (fun uu____10250  ->
                                 let uu____10251 =
                                   FStar_Syntax_Print.pat_to_string p1 in
                                 let uu____10252 =
                                   let uu____10253 =
                                     FStar_List.map
                                       FStar_Syntax_Print.term_to_string s in
                                   FStar_All.pipe_right uu____10253
                                     (FStar_String.concat "; ") in
                                 FStar_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu____10251 uu____10252);
>>>>>>> origin/master
                            (let env2 =
                               FStar_List.fold_left
                                 (fun env2  ->
                                    fun t1  ->
<<<<<<< HEAD
                                      let uu____10244 =
                                        let uu____10245 =
                                          let uu____10255 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10255, false) in
                                        Clos uu____10245 in
                                      uu____10244 :: env2) env1 s in
                             let uu____10278 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10278))) in
                let uu____10279 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10279
=======
                                      let uu____10262 =
                                        let uu____10263 =
                                          let uu____10273 =
                                            FStar_Util.mk_ref (Some ([], t1)) in
                                          ([], t1, uu____10273, false) in
                                        Clos uu____10263 in
                                      uu____10262 :: env2) env1 s in
                             let uu____10296 = guard_when_clause wopt b rest in
                             norm cfg env2 stack2 uu____10296))) in
                let uu____10297 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains (Exclude Iota)) in
                if uu____10297
>>>>>>> origin/master
                then norm_and_rebuild_match ()
                else matches scrutinee branches))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
<<<<<<< HEAD
             (fun uu___141_10293  ->
                match uu___141_10293 with
=======
             (fun uu___140_10311  ->
                match uu___140_10311 with
>>>>>>> origin/master
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
<<<<<<< HEAD
                | uu____10296 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10300 -> d in
=======
                | uu____10314 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____10318 -> d in
>>>>>>> origin/master
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
<<<<<<< HEAD
            let uu___195_10320 = config s e in
            {
              steps = (uu___195_10320.steps);
              tcenv = (uu___195_10320.tcenv);
              delta_level = (uu___195_10320.delta_level);
=======
            let uu___193_10338 = config s e in
            {
              steps = (uu___193_10338.steps);
              tcenv = (uu___193_10338.tcenv);
              delta_level = (uu___193_10338.delta_level);
>>>>>>> origin/master
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
<<<<<<< HEAD
      fun t  -> let uu____10339 = config s e in norm_comp uu____10339 [] t
=======
      fun t  -> let uu____10357 = config s e in norm_comp uu____10357 [] t
>>>>>>> origin/master
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
<<<<<<< HEAD
      let uu____10346 = config [] env in norm_universe uu____10346 [] u
=======
      let uu____10364 = config [] env in norm_universe uu____10364 [] u
>>>>>>> origin/master
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun c  ->
<<<<<<< HEAD
      let uu____10353 = config [] env in ghost_to_pure_aux uu____10353 [] c
=======
      let uu____10371 = config [] env in ghost_to_pure_aux uu____10371 [] c
>>>>>>> origin/master
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
<<<<<<< HEAD
        let uu____10365 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10365 in
      let uu____10366 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10366
=======
        let uu____10383 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____10383 in
      let uu____10384 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____10384
>>>>>>> origin/master
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | Some pure_eff ->
<<<<<<< HEAD
            let uu___196_10368 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___196_10368.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___196_10368.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10369  ->
                    let uu____10370 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10370))
=======
            let uu___194_10386 = lc in
            {
              FStar_Syntax_Syntax.eff_name = pure_eff;
              FStar_Syntax_Syntax.res_typ =
                (uu___194_10386.FStar_Syntax_Syntax.res_typ);
              FStar_Syntax_Syntax.cflags =
                (uu___194_10386.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                ((fun uu____10387  ->
                    let uu____10388 = lc.FStar_Syntax_Syntax.comp () in
                    ghost_to_pure env uu____10388))
>>>>>>> origin/master
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
<<<<<<< HEAD
            ((let uu____10383 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10383);
=======
            ((let uu____10401 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10401);
>>>>>>> origin/master
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
<<<<<<< HEAD
          let uu____10392 = config [AllowUnboundUniverses] env in
          norm_comp uu____10392 [] c
        with
        | e ->
            ((let uu____10396 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10396);
=======
          let uu____10410 = config [AllowUnboundUniverses] env in
          norm_comp uu____10410 [] c
        with
        | e ->
            ((let uu____10414 = FStar_Util.message_of_exn e in
              FStar_Util.print1_warning "Normalization failed with error %s"
                uu____10414);
>>>>>>> origin/master
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
<<<<<<< HEAD
                   let uu____10433 =
                     let uu____10434 =
                       let uu____10439 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10439) in
                     FStar_Syntax_Syntax.Tm_refine uu____10434 in
                   mk uu____10433 t01.FStar_Syntax_Syntax.pos
               | uu____10444 -> t2)
          | uu____10445 -> t2 in
=======
                   let uu____10451 =
                     let uu____10452 =
                       let uu____10457 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____10457) in
                     FStar_Syntax_Syntax.Tm_refine uu____10452 in
                   mk uu____10451 t01.FStar_Syntax_Syntax.pos
               | uu____10462 -> t2)
          | uu____10463 -> t2 in
>>>>>>> origin/master
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
<<<<<<< HEAD
        let uu____10467 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10467 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10483 ->
                 let uu____10487 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10487 with
                  | (actuals,uu____10498,uu____10499) ->
=======
        let uu____10485 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____10485 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____10501 ->
                 let uu____10505 = FStar_Syntax_Util.abs_formals e in
                 (match uu____10505 with
                  | (actuals,uu____10516,uu____10517) ->
>>>>>>> origin/master
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
<<<<<<< HEAD
                        (let uu____10521 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10521 with
                         | (binders,args) ->
                             let uu____10531 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10534 =
                               let uu____10541 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10541
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10531
                               uu____10534)))
=======
                        (let uu____10539 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____10539 with
                         | (binders,args) ->
                             let uu____10549 =
                               FStar_Syntax_Syntax.mk_Tm_app e args None
                                 e.FStar_Syntax_Syntax.pos in
                             let uu____10552 =
                               let uu____10559 =
                                 FStar_All.pipe_right
                                   (FStar_Syntax_Util.lcomp_of_comp c)
                                   (fun _0_44  -> FStar_Util.Inl _0_44) in
                               FStar_All.pipe_right uu____10559
                                 (fun _0_45  -> Some _0_45) in
                             FStar_Syntax_Util.abs binders uu____10549
                               uu____10552)))
>>>>>>> origin/master
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
<<<<<<< HEAD
      let uu____10577 =
        let uu____10581 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10581, (t.FStar_Syntax_Syntax.n)) in
      match uu____10577 with
      | (Some sort,uu____10588) ->
          let uu____10590 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10590
      | (uu____10591,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10595 ->
          let uu____10599 = FStar_Syntax_Util.head_and_args t in
          (match uu____10599 with
           | (head1,args) ->
               let uu____10625 =
                 let uu____10626 = FStar_Syntax_Subst.compress head1 in
                 uu____10626.FStar_Syntax_Syntax.n in
               (match uu____10625 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10629,thead) ->
                    let uu____10647 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10647 with
=======
      let uu____10595 =
        let uu____10599 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
        (uu____10599, (t.FStar_Syntax_Syntax.n)) in
      match uu____10595 with
      | (Some sort,uu____10606) ->
          let uu____10608 = mk sort t.FStar_Syntax_Syntax.pos in
          eta_expand_with_type env t uu____10608
      | (uu____10609,FStar_Syntax_Syntax.Tm_name x) ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____10613 ->
          let uu____10617 = FStar_Syntax_Util.head_and_args t in
          (match uu____10617 with
           | (head1,args) ->
               let uu____10643 =
                 let uu____10644 = FStar_Syntax_Subst.compress head1 in
                 uu____10644.FStar_Syntax_Syntax.n in
               (match uu____10643 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____10647,thead) ->
                    let uu____10661 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____10661 with
>>>>>>> origin/master
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
<<<<<<< HEAD
                           (let uu____10678 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___201_10682 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___201_10682.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___201_10682.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___201_10682.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___201_10682.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___201_10682.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___201_10682.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___201_10682.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___201_10682.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___201_10682.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___201_10682.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___201_10682.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___201_10682.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___201_10682.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___201_10682.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___201_10682.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___201_10682.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___201_10682.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___201_10682.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___201_10682.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___201_10682.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___201_10682.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____10678 with
                            | (uu____10683,ty,uu____10685) ->
                                eta_expand_with_type env t ty))
                | uu____10686 ->
                    let uu____10687 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___202_10691 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___202_10691.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___202_10691.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___202_10691.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___202_10691.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___202_10691.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___202_10691.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___202_10691.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___202_10691.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___202_10691.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___202_10691.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___202_10691.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___202_10691.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___202_10691.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___202_10691.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___202_10691.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___202_10691.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___202_10691.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___202_10691.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___202_10691.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___202_10691.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___202_10691.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____10687 with
                     | (uu____10692,ty,uu____10694) ->
                         eta_expand_with_type env t ty)))
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list*
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.comp',Prims.unit)
                                        FStar_Syntax_Syntax.syntax)
            FStar_Util.either)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____10740,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c)) None
                  c.FStar_Syntax_Syntax.pos
            | (uu____10748,FStar_Util.Inl t) ->
                let uu____10752 =
                  let uu____10755 =
                    let uu____10756 =
                      let uu____10764 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____10764) in
                    FStar_Syntax_Syntax.Tm_arrow uu____10756 in
                  FStar_Syntax_Syntax.mk uu____10755 in
                uu____10752 None t.FStar_Syntax_Syntax.pos in
          let uu____10773 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____10773 with
          | (univ_names1,t1) ->
              let t2 = reduce_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____10790 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____10822 ->
                    let uu____10823 =
                      let uu____10828 =
                        let uu____10829 = FStar_Syntax_Subst.compress t3 in
                        uu____10829.FStar_Syntax_Syntax.n in
                      (uu____10828, tc) in
                    (match uu____10823 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____10845) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____10869) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____10895,FStar_Util.Inl uu____10896) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____10910 -> failwith "Impossible") in
              (match uu____10790 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____10975 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____10975 with
          | (univ_names1,binders1,tc) ->
              let uu____11009 = FStar_Util.left tc in
              (univ_names1, binders1, uu____11009)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
            FStar_Syntax_Syntax.aqual) Prims.list*
            (FStar_Syntax_Syntax.comp',Prims.unit)
            FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____11035 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____11035 with
          | (univ_names1,binders1,tc) ->
              let uu____11071 = FStar_Util.right tc in
              (univ_names1, binders1, uu____11071)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____11097 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____11097 with
           | (univ_names1,binders1,typ1) ->
               let uu___203_11113 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___203_11113.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___203_11113.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___203_11113.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___204_11125 = s in
          let uu____11126 =
            let uu____11127 =
              let uu____11132 = FStar_List.map (elim_uvars env) sigs in
              (uu____11132, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____11127 in
          {
            FStar_Syntax_Syntax.sigel = uu____11126;
            FStar_Syntax_Syntax.sigrng =
              (uu___204_11125.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___204_11125.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___204_11125.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____11144 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11144 with
           | (univ_names1,uu____11154,typ1) ->
               let uu___205_11162 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_11162.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_11162.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_11162.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____11167 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____11167 with
           | (univ_names1,uu____11177,typ1) ->
               let uu___206_11185 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_11185.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_11185.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_11185.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids,attrs) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____11204 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____11204 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____11219 =
                            let uu____11220 =
                              FStar_Syntax_Subst.subst opening t in
                            reduce_uvar_solutions env uu____11220 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____11219 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___207_11223 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___207_11223.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___207_11223.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___208_11224 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids, attrs));
            FStar_Syntax_Syntax.sigrng =
              (uu___208_11224.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_11224.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_11224.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___209_11232 = s in
          let uu____11233 =
            let uu____11234 = reduce_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____11234 in
          {
            FStar_Syntax_Syntax.sigel = uu____11233;
            FStar_Syntax_Syntax.sigrng =
              (uu___209_11232.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_11232.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_11232.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____11238 = elim_uvars_aux_t env us [] t in
          (match uu____11238 with
           | (us1,uu____11248,t1) ->
               let uu___210_11256 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___210_11256.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___210_11256.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___210_11256.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11257 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11259 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____11259 with
           | (univs1,binders,signature) ->
               let uu____11275 =
                 let uu____11280 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____11280 with
                 | (univs_opening,univs2) ->
                     let uu____11295 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____11295) in
               (match uu____11275 with
                | (univs_opening,univs_closing) ->
                    let uu____11305 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____11309 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____11310 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____11309, uu____11310) in
                    (match uu____11305 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____11327 =
                           match uu____11327 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____11339 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____11339 with
                                | (us1,t1) ->
                                    let uu____11346 =
                                      let uu____11349 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____11353 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____11349, uu____11353) in
                                    (match uu____11346 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____11361 =
                                           let uu____11364 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____11369 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____11364, uu____11369) in
                                         (match uu____11361 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____11379 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____11379 in
                                              let uu____11380 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____11380 with
                                               | (uu____11391,uu____11392,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____11401 =
                                                       let uu____11402 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____11402 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____11401 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____11407 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____11407 with
                           | (uu____11414,uu____11415,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_ascribed
                                   ((a.FStar_Syntax_Syntax.action_defn),
                                     ((FStar_Util.Inl
                                         (a.FStar_Syntax_Syntax.action_typ)),
                                       None), None))) None
                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_typ_templ t =
                             let uu____11469 =
                               let uu____11470 =
                                 FStar_Syntax_Subst.compress t in
                               uu____11470.FStar_Syntax_Syntax.n in
                             match uu____11469 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl typ,None ),None ) ->
                                 (defn, typ)
                             | uu____11518 -> failwith "Impossible" in
                           let uu____11525 =
                             elim_uvars_aux_t env
                               (FStar_List.append univs1
                                  a.FStar_Syntax_Syntax.action_univs)
                               (FStar_List.append binders
                                  a.FStar_Syntax_Syntax.action_params)
                               action_typ_templ in
                           match uu____11525 with
                           | (u_action_univs,b_action_params,res) ->
                               let action_univs =
                                 FStar_Util.nth_tail n1 u_action_univs in
                               let action_params =
                                 FStar_Util.nth_tail
                                   (FStar_List.length binders)
                                   b_action_params in
                               let uu____11557 =
                                 destruct_action_typ_templ res in
                               (match uu____11557 with
                                | (action_defn,action_typ) ->
                                    let uu___211_11574 = a in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        (uu___211_11574.FStar_Syntax_Syntax.action_name);
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (uu___211_11574.FStar_Syntax_Syntax.action_unqualified_name);
                                      FStar_Syntax_Syntax.action_univs =
                                        action_univs;
                                      FStar_Syntax_Syntax.action_params =
                                        action_params;
                                      FStar_Syntax_Syntax.action_defn =
                                        action_defn;
                                      FStar_Syntax_Syntax.action_typ =
                                        action_typ
                                    }) in
                         let ed1 =
                           let uu___212_11576 = ed in
                           let uu____11577 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____11578 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____11579 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____11580 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____11581 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____11582 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____11583 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____11584 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____11585 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____11586 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____11587 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____11588 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____11589 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____11590 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___212_11576.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___212_11576.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____11577;
                             FStar_Syntax_Syntax.bind_wp = uu____11578;
                             FStar_Syntax_Syntax.if_then_else = uu____11579;
                             FStar_Syntax_Syntax.ite_wp = uu____11580;
                             FStar_Syntax_Syntax.stronger = uu____11581;
                             FStar_Syntax_Syntax.close_wp = uu____11582;
                             FStar_Syntax_Syntax.assert_p = uu____11583;
                             FStar_Syntax_Syntax.assume_p = uu____11584;
                             FStar_Syntax_Syntax.null_wp = uu____11585;
                             FStar_Syntax_Syntax.trivial = uu____11586;
                             FStar_Syntax_Syntax.repr = uu____11587;
                             FStar_Syntax_Syntax.return_repr = uu____11588;
                             FStar_Syntax_Syntax.bind_repr = uu____11589;
                             FStar_Syntax_Syntax.actions = uu____11590
                           } in
                         let uu___213_11592 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___213_11592.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___213_11592.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___213_11592.FStar_Syntax_Syntax.sigmeta)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___142_11603 =
            match uu___142_11603 with
            | None  -> None
            | Some (us,t) ->
                let uu____11618 = elim_uvars_aux_t env us [] t in
                (match uu____11618 with
                 | (us1,uu____11631,t1) -> Some (us1, t1)) in
          let sub_eff1 =
            let uu___214_11642 = sub_eff in
            let uu____11643 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____11645 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___214_11642.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___214_11642.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____11643;
              FStar_Syntax_Syntax.lift = uu____11645
            } in
          let uu___215_11647 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___215_11647.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___215_11647.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___215_11647.FStar_Syntax_Syntax.sigmeta)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____11655 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____11655 with
           | (univ_names1,binders1,comp1) ->
               let uu___216_11677 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_11677.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_11677.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_11677.FStar_Syntax_Syntax.sigmeta)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____11684 -> s
=======
                           (let uu____10692 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___199_10696 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___199_10696.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___199_10696.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___199_10696.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___199_10696.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___199_10696.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___199_10696.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ = None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___199_10696.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___199_10696.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___199_10696.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___199_10696.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___199_10696.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___199_10696.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___199_10696.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___199_10696.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___199_10696.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___199_10696.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___199_10696.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___199_10696.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___199_10696.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___199_10696.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___199_10696.FStar_TypeChecker_Env.qname_and_index)
                                 }) t in
                            match uu____10692 with
                            | (uu____10697,ty,uu____10699) ->
                                eta_expand_with_type env t ty))
                | uu____10700 ->
                    let uu____10701 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___200_10705 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___200_10705.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___200_10705.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___200_10705.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___200_10705.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___200_10705.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___200_10705.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ = None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___200_10705.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___200_10705.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___200_10705.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___200_10705.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___200_10705.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___200_10705.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___200_10705.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___200_10705.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___200_10705.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___200_10705.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___200_10705.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___200_10705.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___200_10705.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___200_10705.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___200_10705.FStar_TypeChecker_Env.qname_and_index)
                         }) t in
                    (match uu____10701 with
                     | (uu____10706,ty,uu____10708) ->
                         eta_expand_with_type env t ty)))
>>>>>>> origin/master
