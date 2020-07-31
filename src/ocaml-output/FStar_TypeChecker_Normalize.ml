open Prims
let cases :
  'uuuuuu10 'uuuuuu11 .
    ('uuuuuu10 -> 'uuuuuu11) ->
      'uuuuuu11 -> 'uuuuuu10 FStar_Pervasives_Native.option -> 'uuuuuu11
  =
  fun f ->
    fun d ->
      fun uu___0_31 ->
        match uu___0_31 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None -> d
type closure =
  | Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option *
  closure) Prims.list * FStar_Syntax_Syntax.term *
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
  Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo *
  Prims.bool) 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee ->
    match projectee with | Clos _0 -> true | uu____115 -> false
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee -> match projectee with | Clos _0 -> _0
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee ->
    match projectee with | Univ _0 -> true | uu____218 -> false
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee -> match projectee with | Dummy -> true | uu____230 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)) =
  (FStar_Pervasives_Native.None, Dummy)
type branches =
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list
type stack_elt =
  | Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
  
  | MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo 
  | Match of (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range)
  
  | Abs of (env * FStar_Syntax_Syntax.binders * env *
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStar_Range.range) 
  | App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | CBVApp of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) 
  | Let of (env * FStar_Syntax_Syntax.binders *
  FStar_Syntax_Syntax.letbinding * FStar_Range.range) 
  | Cfg of FStar_TypeChecker_Cfg.cfg 
  | Debug of (FStar_Syntax_Syntax.term * FStar_Util.time) 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Arg _0 -> true | uu____398 -> false
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivArgs _0 -> true | uu____435 -> false
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | MemoLazy _0 -> true | uu____472 -> false
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____511 -> false
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu____560 -> false
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu____617 -> false
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | App _0 -> _0
let (uu___is_CBVApp : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | CBVApp _0 -> true | uu____662 -> false
let (__proj__CBVApp__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | CBVApp _0 -> _0
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____705 -> false
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu____744 -> false
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Cfg _0 -> true | uu____781 -> false
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee -> match projectee with | Cfg _0 -> _0
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Debug _0 -> true | uu____798 -> false
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____824 = FStar_Syntax_Util.head_and_args' t in
    match uu____824 with | (hd, uu____840) -> hd
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg ->
    fun r ->
      fun t ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu____889 = FStar_ST.op_Bang r in
          match uu____889 with
          | FStar_Pervasives_Native.Some uu____902 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let (closure_to_string : closure -> Prims.string) =
  fun uu___1_918 ->
    match uu___1_918 with
    | Clos (env1, t, uu____921, uu____922) ->
        let uu____967 =
          FStar_All.pipe_right (FStar_List.length env1)
            FStar_Util.string_of_int in
        let uu____974 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2 "(env=%s elts; %s)" uu____967 uu____974
    | Univ uu____975 -> "Univ"
    | Dummy -> "dummy"
let (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env1 ->
    let uu____997 =
      FStar_List.map
        (fun uu____1011 ->
           match uu____1011 with
           | (bopt, c) ->
               let uu____1024 =
                 match bopt with
                 | FStar_Pervasives_Native.None -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x in
               let uu____1026 = closure_to_string c in
               FStar_Util.format2 "(%s, %s)" uu____1024 uu____1026) env1 in
    FStar_All.pipe_right uu____997 (FStar_String.concat "; ")
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1033 ->
    match uu___2_1033 with
    | Arg (c, uu____1035, uu____1036) ->
        let uu____1037 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1037
    | MemoLazy uu____1038 -> "MemoLazy"
    | Abs (uu____1045, bs, uu____1047, uu____1048, uu____1049) ->
        let uu____1054 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1054
    | UnivArgs uu____1061 -> "UnivArgs"
    | Match uu____1068 -> "Match"
    | App (uu____1077, t, uu____1079, uu____1080) ->
        let uu____1081 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1081
    | CBVApp (uu____1082, t, uu____1084, uu____1085) ->
        let uu____1086 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "CBVApp %s" uu____1086
    | Meta (uu____1087, m, uu____1089) -> "Meta"
    | Let uu____1090 -> "Let"
    | Cfg uu____1099 -> "Cfg"
    | Debug (t, uu____1101) ->
        let uu____1102 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1102
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s ->
    let uu____1112 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1112 (FStar_String.concat "; ")
let is_empty : 'uuuuuu1121 . 'uuuuuu1121 Prims.list -> Prims.bool =
  fun uu___3_1128 ->
    match uu___3_1128 with | [] -> true | uu____1131 -> false
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env1 ->
    fun x ->
      try
        (fun uu___119_1162 ->
           match () with
           | () ->
               let uu____1163 =
                 FStar_List.nth env1 x.FStar_Syntax_Syntax.index in
               FStar_Pervasives_Native.snd uu____1163) ()
      with
      | uu___118_1180 ->
          let uu____1181 =
            let uu____1182 = FStar_Syntax_Print.db_to_string x in
            let uu____1183 = env_to_string env1 in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1182
              uu____1183 in
          failwith uu____1181
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l ->
    let uu____1191 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid in
    if uu____1191
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1195 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid in
       if uu____1195
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1199 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid in
          if uu____1199
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
let (norm_universe :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg ->
    fun env1 ->
      fun u ->
        let norm_univs_for_max us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____1233 =
            FStar_List.fold_left
              (fun uu____1259 ->
                 fun u1 ->
                   match uu____1259 with
                   | (cur_kernel, cur_max, out) ->
                       let uu____1284 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1284 with
                        | (k_u, n) ->
                            let uu____1299 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1299
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1233 with
          | (uu____1317, u1, out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___153_1344 ->
                    match () with
                    | () ->
                        let uu____1347 =
                          let uu____1348 = FStar_List.nth env1 x in
                          FStar_Pervasives_Native.snd uu____1348 in
                        (match uu____1347 with
                         | Univ u3 ->
                             ((let uu____1367 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm") in
                               if uu____1367
                               then
                                 let uu____1368 =
                                   FStar_Syntax_Print.univ_to_string u3 in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1368
                               else ());
                              aux u3)
                         | Dummy -> [u2]
                         | uu____1370 ->
                             let uu____1371 =
                               let uu____1372 = FStar_Util.string_of_int x in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1372 in
                             failwith uu____1371)) ()
               with
               | uu____1380 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1384 =
                        let uu____1385 = FStar_Util.string_of_int x in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1385 in
                      failwith uu____1384))
          | FStar_Syntax_Syntax.U_unif uu____1388 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1399 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1410 -> [u2]
          | FStar_Syntax_Syntax.U_unknown -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1417 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1417 norm_univs_for_max in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest in
                   let uu____1434 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1434 with
                    | (FStar_Syntax_Syntax.U_zero, n) ->
                        let uu____1442 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3 ->
                                  let uu____1450 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1450 with
                                  | (uu____1455, m) -> n <= m)) in
                        if uu____1442 then rest1 else us1
                    | uu____1460 -> us1)
               | uu____1465 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1469 = aux u3 in
              FStar_List.map
                (fun uu____1472 -> FStar_Syntax_Syntax.U_succ uu____1472)
                uu____1469 in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1474 = aux u in
           match uu____1474 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero)::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero)::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero)::us -> FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec (inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____1634 ->
               let uu____1635 = FStar_Syntax_Print.tag_of_term t in
               let uu____1636 = env_to_string env1 in
               let uu____1637 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print3 ">>> %s (env=%s)\nClosure_as_term %s\n"
                 uu____1635 uu____1636 uu____1637);
          (match env1 with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env1 stack1 t
           | uu____1646 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1649 ->
                    let uu____1664 = FStar_Syntax_Subst.compress t in
                    inline_closure_env cfg env1 stack1 uu____1664
                | FStar_Syntax_Syntax.Tm_unknown ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_constant uu____1665 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_name uu____1666 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_lazy uu____1667 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_fvar uu____1668 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1692 ->
                           let uu____1705 =
                             let uu____1706 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos in
                             let uu____1707 =
                               FStar_Syntax_Print.term_to_string t1 in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1706 uu____1707 in
                           failwith uu____1705
                       | uu____1710 -> inline_closure_env cfg env1 stack1 t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1 ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_1745 ->
                                         match uu___4_1745 with
                                         | FStar_Syntax_Syntax.NT (x, t1) ->
                                             let uu____1752 =
                                               let uu____1759 =
                                                 inline_closure_env cfg env1
                                                   [] t1 in
                                               (x, uu____1759) in
                                             FStar_Syntax_Syntax.NT
                                               uu____1752
                                         | FStar_Syntax_Syntax.NM (x, i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___247_1769 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___247_1769.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___247_1769.FStar_Syntax_Syntax.sort)
                                                  }) in
                                             let t1 =
                                               inline_closure_env cfg env1 []
                                                 x_i in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu____1774 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1777 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes")))) in
                       let t1 =
                         let uu___256_1781 = t in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___256_1781.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___256_1781.FStar_Syntax_Syntax.vars)
                         } in
                       rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____1802 =
                        let uu____1803 = norm_universe cfg env1 u in
                        FStar_Syntax_Syntax.Tm_type uu____1803 in
                      FStar_Syntax_Syntax.mk uu____1802
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
                    let t1 =
                      let uu____1811 =
                        FStar_List.map (norm_universe cfg env1) us in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1811 in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____1813 = lookup_bvar env1 x in
                    (match uu____1813 with
                     | Univ uu____1816 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy ->
                         let x1 =
                           let uu___272_1820 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___272_1820.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___272_1820.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1
                     | Clos (env2, t0, uu____1826, uu____1827) ->
                         inline_closure_env cfg env2 stack1 t0)
                | FStar_Syntax_Syntax.Tm_app (head, args) ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____1916 ->
                              fun stack2 ->
                                match uu____1916 with
                                | (a, aq) ->
                                    let uu____1928 =
                                      let uu____1929 =
                                        let uu____1936 =
                                          let uu____1937 =
                                            let uu____1968 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu____1968, false) in
                                          Clos uu____1937 in
                                        (uu____1936, aq,
                                          (t.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____1929 in
                                    uu____1928 :: stack2) args) in
                    inline_closure_env cfg env1 stack2 head
                | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
                    let env' =
                      FStar_All.pipe_right env1
                        (FStar_List.fold_right
                           (fun _b ->
                              fun env2 ->
                                (FStar_Pervasives_Native.None, Dummy) :: env2)
                           bs) in
                    let stack2 =
                      (Abs
                         (env1, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    inline_closure_env cfg env' stack2 body
                | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                    let uu____2134 = close_binders cfg env1 bs in
                    (match uu____2134 with
                     | (bs1, env') ->
                         let c1 = close_comp cfg env' c in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_refine (x, uu____2184) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env1 stack1
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
                    let uu____2195 =
                      let uu____2208 =
                        let uu____2217 = FStar_Syntax_Syntax.mk_binder x in
                        [uu____2217] in
                      close_binders cfg env1 uu____2208 in
                    (match uu____2195 with
                     | (x1, env2) ->
                         let phi1 = non_tail_inline_closure_env cfg env2 phi in
                         let t1 =
                           let uu____2262 =
                             let uu____2263 =
                               let uu____2270 =
                                 let uu____2271 = FStar_List.hd x1 in
                                 FStar_All.pipe_right uu____2271
                                   FStar_Pervasives_Native.fst in
                               (uu____2270, phi1) in
                             FStar_Syntax_Syntax.Tm_refine uu____2263 in
                           FStar_Syntax_Syntax.mk uu____2262
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env2 stack1 t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt)
                    ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2370 =
                            non_tail_inline_closure_env cfg env1 t2 in
                          FStar_Util.Inl uu____2370
                      | FStar_Util.Inr c ->
                          let uu____2384 = close_comp cfg env1 c in
                          FStar_Util.Inr uu____2384 in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env1) in
                    let t2 =
                      let uu____2403 =
                        let uu____2404 =
                          let uu____2431 =
                            non_tail_inline_closure_env cfg env1 t1 in
                          (uu____2431, (annot1, tacopt1), lopt) in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2404 in
                      FStar_Syntax_Syntax.mk uu____2403
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t2
                | FStar_Syntax_Syntax.Tm_quoted (t', qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic ->
                          let uu____2477 =
                            let uu____2478 =
                              let uu____2485 =
                                non_tail_inline_closure_env cfg env1 t' in
                              (uu____2485, qi) in
                            FStar_Syntax_Syntax.Tm_quoted uu____2478 in
                          FStar_Syntax_Syntax.mk uu____2477
                            t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env1) qi in
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_meta (t', m) ->
                    let stack2 =
                      (Meta (env1, m, (t.FStar_Syntax_Syntax.pos))) :: stack1 in
                    inline_closure_env cfg env1 stack2 t'
                | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                    let env0 = env1 in
                    let env2 =
                      FStar_List.fold_left
                        (fun env2 -> fun uu____2537 -> dummy :: env2) env1
                        lb.FStar_Syntax_Syntax.lbunivs in
                    let typ =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let def =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbdef in
                    let uu____2558 =
                      let uu____2569 = FStar_Syntax_Syntax.is_top_level [lb] in
                      if uu____2569
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         let uu____2588 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body in
                         ((FStar_Util.Inl
                             (let uu___364_2604 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___364_2604.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___364_2604.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2588)) in
                    (match uu____2558 with
                     | (nm, body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs in
                         let lb1 =
                           let uu___370_2631 = lb in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___370_2631.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___370_2631.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___370_2631.FStar_Syntax_Syntax.lbpos)
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env0 stack1 t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2645, lbs), body) ->
                    let norm_one_lb env2 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2708 -> fun env3 -> dummy :: env3)
                          lb.FStar_Syntax_Syntax.lbunivs env2 in
                      let env3 =
                        let uu____2725 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu____2725
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2737 -> fun env3 -> dummy :: env3) lbs
                            env_univs in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp in
                      let nm =
                        let uu____2761 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu____2761
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           FStar_Util.Inl
                             (let uu___393_2769 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___393_2769.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___393_2769.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              })) in
                      let uu___396_2770 = lb in
                      let uu____2771 =
                        non_tail_inline_closure_env cfg env3
                          lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___396_2770.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___396_2770.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2771;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___396_2770.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___396_2770.FStar_Syntax_Syntax.lbpos)
                      } in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env1)) in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____2803 -> fun env2 -> dummy :: env2) lbs1
                          env1 in
                      non_tail_inline_closure_env cfg body_env body in
                    let t1 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_match (head, branches1) ->
                    let stack2 =
                      (Match
                         (env1, branches1, cfg, (t.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    inline_closure_env cfg env1 stack2 head))
and (non_tail_inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg -> fun env1 -> fun t -> inline_closure_env cfg env1 [] t
and (rebuild_closure :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____2892 ->
               let uu____2893 = FStar_Syntax_Print.tag_of_term t in
               let uu____2894 = env_to_string env1 in
               let uu____2895 = stack_to_string stack1 in
               let uu____2896 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu____2893 uu____2894 uu____2895 uu____2896);
          (match stack1 with
           | [] -> t
           | (Arg
               (Clos (env_arg, tm, uu____2901, uu____2902), aq, r))::stack2
               ->
               let stack3 = (App (env1, t, aq, r)) :: stack2 in
               inline_closure_env cfg env_arg stack3 tm
           | (App (env2, head, aq, r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.extend_app head (t, aq) r in
               rebuild_closure cfg env2 stack2 t1
           | (CBVApp (env2, head, aq, r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.extend_app head (t, aq) r in
               rebuild_closure cfg env2 stack2 t1
           | (Abs (env', bs, env'', lopt, r))::stack2 ->
               let uu____2991 = close_binders cfg env' bs in
               (match uu____2991 with
                | (bs1, uu____3007) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt in
                    let uu____3027 =
                      let uu___463_3030 = FStar_Syntax_Util.abs bs1 t lopt1 in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___463_3030.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___463_3030.FStar_Syntax_Syntax.vars)
                      } in
                    rebuild_closure cfg env1 stack2 uu____3027)
           | (Match (env2, branches1, cfg1, r))::stack2 ->
               let close_one_branch env3 uu____3086 =
                 match uu____3086 with
                 | (pat, w_opt, tm) ->
                     let rec norm_pat env4 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3201 ->
                           (p, env4)
                       | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                           let uu____3230 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3314 ->
                                     fun uu____3315 ->
                                       match (uu____3314, uu____3315) with
                                       | ((pats1, env5), (p1, b)) ->
                                           let uu____3454 = norm_pat env5 p1 in
                                           (match uu____3454 with
                                            | (p2, env6) ->
                                                (((p2, b) :: pats1), env6)))
                                  ([], env4)) in
                           (match uu____3230 with
                            | (pats1, env5) ->
                                ((let uu___500_3616 = p in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___500_3616.FStar_Syntax_Syntax.p)
                                  }), env5))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___504_3635 = x in
                             let uu____3636 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___504_3635.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___504_3635.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3636
                             } in
                           ((let uu___507_3650 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___507_3650.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___511_3661 = x in
                             let uu____3662 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___511_3661.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___511_3661.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3662
                             } in
                           ((let uu___514_3676 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___514_3676.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_dot_term (x, t1) ->
                           let x1 =
                             let uu___520_3692 = x in
                             let uu____3693 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___520_3692.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___520_3692.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3693
                             } in
                           let t2 = non_tail_inline_closure_env cfg1 env4 t1 in
                           ((let uu___524_3710 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___524_3710.FStar_Syntax_Syntax.p)
                             }), env4) in
                     let uu____3715 = norm_pat env3 pat in
                     (match uu____3715 with
                      | (pat1, env4) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____3784 =
                                  non_tail_inline_closure_env cfg1 env4 w in
                                FStar_Pervasives_Native.Some uu____3784 in
                          let tm1 = non_tail_inline_closure_env cfg1 env4 tm in
                          (pat1, w_opt1, tm1)) in
               let t1 =
                 let uu____3803 =
                   let uu____3804 =
                     let uu____3827 =
                       FStar_All.pipe_right branches1
                         (FStar_List.map (close_one_branch env2)) in
                     (t, uu____3827) in
                   FStar_Syntax_Syntax.Tm_match uu____3804 in
                 FStar_Syntax_Syntax.mk uu____3803 t.FStar_Syntax_Syntax.pos in
               rebuild_closure cfg1 env2 stack2 t1
           | (Meta (env_m, m, r))::stack2 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
                     let uu____3963 =
                       let uu____3984 =
                         FStar_All.pipe_right names
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m)) in
                       let uu____4001 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1 ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4110 ->
                                         match uu____4110 with
                                         | (a, q) ->
                                             let uu____4137 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a in
                                             (uu____4137, q))))) in
                       (uu____3984, uu____4001) in
                     FStar_Syntax_Syntax.Meta_pattern uu____3963
                 | FStar_Syntax_Syntax.Meta_monadic (m1, tbody) ->
                     let uu____4166 =
                       let uu____4173 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m1, uu____4173) in
                     FStar_Syntax_Syntax.Meta_monadic uu____4166
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) ->
                     let uu____4185 =
                       let uu____4194 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m1, m2, uu____4194) in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4185
                 | uu____4199 -> m in
               let t1 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (t, m1))
                   r in
               rebuild_closure cfg env1 stack2 t1
           | uu____4205 -> failwith "Impossible: unexpected stack element")
and (close_imp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env1 ->
      fun imp ->
        match imp with
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
            (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
            let uu____4220 =
              let uu____4221 =
                let uu____4222 = inline_closure_env cfg env1 [] t in
                FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____4222 in
              FStar_Syntax_Syntax.Meta uu____4221 in
            FStar_Pervasives_Native.Some uu____4220
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
            let uu____4228 =
              let uu____4229 =
                let uu____4230 = inline_closure_env cfg env1 [] t in
                FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____4230 in
              FStar_Syntax_Syntax.Meta uu____4229 in
            FStar_Pervasives_Native.Some uu____4228
        | i -> i
and (close_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list * env))
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu____4247 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4331 ->
                  fun uu____4332 ->
                    match (uu____4331, uu____4332) with
                    | ((env2, out), (b, imp)) ->
                        let b1 =
                          let uu___584_4472 = b in
                          let uu____4473 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___584_4472.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___584_4472.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4473
                          } in
                        let imp1 = close_imp cfg env2 imp in
                        let env3 = dummy :: env2 in
                        (env3, ((b1, imp1) :: out))) (env1, [])) in
        match uu____4247 with | (env2, bs1) -> ((FStar_List.rev bs1), env2)
and (close_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env1 ->
      fun c ->
        match env1 with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
            -> c
        | uu____4613 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t, uopt) ->
                 let uu____4626 = inline_closure_env cfg env1 [] t in
                 let uu____4627 =
                   FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4626 uu____4627
             | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                 let uu____4640 = inline_closure_env cfg env1 [] t in
                 let uu____4641 =
                   FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4640 uu____4641
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4695 ->
                           match uu____4695 with
                           | (a, q) ->
                               let uu____4716 =
                                 inline_closure_env cfg env1 [] a in
                               (uu____4716, q))) in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_4733 ->
                           match uu___5_4733 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4737 =
                                 inline_closure_env cfg env1 [] t in
                               FStar_Syntax_Syntax.DECREASES uu____4737
                           | f -> f)) in
                 let uu____4741 =
                   let uu___617_4742 = c1 in
                   let uu____4743 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4743;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___617_4742.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____4741)
and (close_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env1 ->
      fun lopt ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___6_4761 ->
                      match uu___6_4761 with
                      | FStar_Syntax_Syntax.DECREASES uu____4762 -> false
                      | uu____4765 -> true)) in
            let rc1 =
              let uu___629_4767 = rc in
              let uu____4768 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___629_4767.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4768;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____4777 -> lopt
let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_4797 ->
            match uu___7_4797 with
            | FStar_Syntax_Syntax.DECREASES uu____4798 -> false
            | uu____4801 -> true))
let (closure_as_term :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun cfg -> fun env1 -> fun t -> non_tail_inline_closure_env cfg env1 t
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____4844 = FStar_ST.op_Bang unembed_binder_knot in
    match uu____4844 with
    | FStar_Pervasives_Native.Some e ->
        let uu____4870 = FStar_Syntax_Embeddings.unembed e t in
        uu____4870 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
let mk_psc_subst :
  'uuuuuu4886 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'uuuuuu4886) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg ->
    fun env1 ->
      FStar_List.fold_right
        (fun uu____4948 ->
           fun subst ->
             match uu____4948 with
             | (binder_opt, closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b, Clos
                     (env2, term, uu____4989, uu____4990)) ->
                      let uu____5049 = b in
                      (match uu____5049 with
                       | (bv, uu____5057) ->
                           let uu____5058 =
                             let uu____5059 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid in
                             Prims.op_Negation uu____5059 in
                           if uu____5058
                           then subst
                           else
                             (let term1 = closure_as_term cfg env2 term in
                              let uu____5064 = unembed_binder term1 in
                              match uu____5064 with
                              | FStar_Pervasives_Native.None -> subst
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5071 =
                                      let uu___669_5072 = bv in
                                      let uu____5073 =
                                        FStar_Syntax_Subst.subst subst
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___669_5072.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___669_5072.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5073
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____5071 in
                                  let b_for_x =
                                    let uu____5079 =
                                      let uu____5086 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5086) in
                                    FStar_Syntax_Syntax.NT uu____5079 in
                                  let subst1 =
                                    FStar_List.filter
                                      (fun uu___8_5102 ->
                                         match uu___8_5102 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5103,
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  b';
                                                FStar_Syntax_Syntax.pos =
                                                  uu____5105;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____5106;_})
                                             ->
                                             let uu____5111 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname in
                                             Prims.op_Negation uu____5111
                                         | uu____5112 -> true) subst in
                                  b_for_x :: subst1))
                  | uu____5113 -> subst)) env1 []
let reduce_primops :
  'uuuuuu5134 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5134)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb ->
    fun cfg ->
      fun env1 ->
        fun tm ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu____5184 = FStar_Syntax_Util.head_and_args tm in
             match uu____5184 with
             | (head, args) ->
                 let uu____5229 =
                   let uu____5230 = FStar_Syntax_Util.un_uinst head in
                   uu____5230.FStar_Syntax_Syntax.n in
                 (match uu____5229 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5236 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                      (match uu____5236 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok
                             ||
                             (Prims.op_Negation
                                cfg.FStar_TypeChecker_Cfg.strong)
                           ->
                           let l = FStar_List.length args in
                           if l < prim_step.FStar_TypeChecker_Cfg.arity
                           then
                             (FStar_TypeChecker_Cfg.log_primops cfg
                                (fun uu____5258 ->
                                   let uu____5259 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name in
                                   let uu____5260 =
                                     FStar_Util.string_of_int l in
                                   let uu____5261 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5259 uu____5260 uu____5261);
                              tm)
                           else
                             (let uu____5263 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args in
                              match uu____5263 with
                              | (args_1, args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5346 ->
                                        let uu____5347 =
                                          FStar_Syntax_Print.term_to_string
                                            tm in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5347);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5350 ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env1
                                             else [])
                                      } in
                                    let r =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_1 in
                                    match r with
                                    | FStar_Pervasives_Native.None ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5362 ->
                                              let uu____5363 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5363);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5369 ->
                                              let uu____5370 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              let uu____5371 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5370 uu____5371);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5372 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5376 ->
                                 let uu____5377 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5377);
                            tm)
                       | FStar_Pervasives_Native.None -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5381 ->
                            let uu____5382 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5382);
                       (match args with
                        | (a1, uu____5386)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5411 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5425 ->
                            let uu____5426 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5426);
                       (match args with
                        | (t, uu____5430)::(r, uu____5432)::[] ->
                            let uu____5473 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r in
                            (match uu____5473 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None -> tm)
                        | uu____5479 -> tm))
                  | uu____5490 -> tm))
let reduce_equality :
  'uuuuuu5500 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5500)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb ->
    fun cfg ->
      fun tm ->
        reduce_primops norm_cb
          (let uu___757_5549 = cfg in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___759_5552 = FStar_TypeChecker_Cfg.default_steps in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___759_5552.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___759_5552.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___759_5552.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___759_5552.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___759_5552.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___759_5552.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___759_5552.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___759_5552.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___759_5552.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___759_5552.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___759_5552.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___759_5552.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___759_5552.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___759_5552.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___759_5552.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___759_5552.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___759_5552.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___759_5552.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___759_5552.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___759_5552.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___759_5552.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___759_5552.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___759_5552.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___759_5552.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___759_5552.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___759_5552.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___757_5549.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___757_5549.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___757_5549.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___757_5549.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___757_5549.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___757_5549.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___757_5549.FStar_TypeChecker_Cfg.reifying)
           }) tm
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_none -> true | uu____5558 -> false
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_ready -> true | uu____5564 -> false
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Norm_request_requires_rejig -> true
    | uu____5570 -> false
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd ->
    fun args ->
      let aux min_args =
        let uu____5587 = FStar_All.pipe_right args FStar_List.length in
        FStar_All.pipe_right uu____5587
          (fun n ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig) in
      let uu____5610 =
        let uu____5611 = FStar_Syntax_Util.un_uinst hd in
        uu____5611.FStar_Syntax_Syntax.n in
      match uu____5610 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____5617 -> Norm_request_none
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____5624 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid in
       Prims.op_Negation uu____5624)
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd ->
    fun args ->
      let uu____5635 =
        let uu____5636 = FStar_Syntax_Util.un_uinst hd in
        uu____5636.FStar_Syntax_Syntax.n in
      match uu____5635 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____5693 = FStar_Syntax_Util.mk_app hd [t1; t2] in
               FStar_Syntax_Util.mk_app uu____5693 rest
           | uu____5720 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____5758 = FStar_Syntax_Util.mk_app hd [t] in
               FStar_Syntax_Util.mk_app uu____5758 rest
           | uu____5777 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____5849 = FStar_Syntax_Util.mk_app hd [t1; t2; t3] in
               FStar_Syntax_Util.mk_app uu____5849 rest
           | uu____5884 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____5885 ->
          let uu____5886 =
            let uu____5887 = FStar_Syntax_Print.term_to_string hd in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____5887 in
          failwith uu____5886
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_5903 ->
    match uu___9_5903 with
    | FStar_Syntax_Embeddings.Zeta -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.ZetaFull -> [FStar_TypeChecker_Env.ZetaFull]
    | FStar_Syntax_Embeddings.Iota -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.Reify -> [FStar_TypeChecker_Env.Reify]
    | FStar_Syntax_Embeddings.UnfoldOnly names ->
        let uu____5909 =
          let uu____5912 =
            let uu____5913 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldOnly uu____5913 in
          [uu____5912] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5909
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____5919 =
          let uu____5922 =
            let uu____5923 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldFully uu____5923 in
          [uu____5922] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5919
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____5929 =
          let uu____5932 =
            let uu____5933 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldAttr uu____5933 in
          [uu____5932] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5929
    | FStar_Syntax_Embeddings.NBE -> [FStar_TypeChecker_Env.NBE]
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s ->
    let s1 = FStar_List.concatMap tr_norm_step s in
    let add_exclude s2 z =
      let uu____5967 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2 in
      if uu____5967 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2 in
    let s2 = FStar_TypeChecker_Env.Beta :: s1 in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota in s4
let get_norm_request :
  'uuuuuu5988 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu5988) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun full_norm ->
      fun args ->
        let parse_steps s =
          let uu____6039 =
            let uu____6044 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6044 s in
          match uu____6039 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6060 = tr_norm_steps steps in
              FStar_Pervasives_Native.Some uu____6060
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        let inherited_steps =
          FStar_List.append
            (if
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
             then [FStar_TypeChecker_Env.EraseUniverses]
             else [])
            (FStar_List.append
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                then [FStar_TypeChecker_Env.AllowUnboundUniverses]
                else [])
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.nbe_step
                then [FStar_TypeChecker_Env.NBE]
                else [])) in
        match args with
        | uu____6089::(tm, uu____6091)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify] in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm, uu____6120)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify] in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps, uu____6141)::uu____6142::(tm, uu____6144)::[] ->
            let uu____6165 =
              let uu____6170 = full_norm steps in parse_steps uu____6170 in
            (match uu____6165 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6200 -> FStar_Pervasives_Native.None
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun s ->
      fun tm ->
        let delta_level =
          let uu____6231 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6236 ->
                    match uu___10_6236 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6237 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6238 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6241 -> true
                    | uu____6244 -> false)) in
          if uu____6231
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta] in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6251 ->
             let uu____6252 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6252);
        (let tm_norm =
           let uu____6254 = FStar_TypeChecker_Cfg.cfg_env cfg in
           uu____6254.FStar_TypeChecker_Env.nbe s
             cfg.FStar_TypeChecker_Cfg.tcenv tm in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6258 ->
              let uu____6259 = FStar_Syntax_Print.term_to_string tm_norm in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6259);
         tm_norm)
let firstn :
  'uuuuuu6266 .
    Prims.int ->
      'uuuuuu6266 Prims.list ->
        ('uuuuuu6266 Prims.list * 'uuuuuu6266 Prims.list)
  =
  fun k ->
    fun l ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg ->
    fun stack1 ->
      let rec drop_irrel uu___11_6317 =
        match uu___11_6317 with
        | (MemoLazy uu____6322)::s -> drop_irrel s
        | (UnivArgs uu____6332)::s -> drop_irrel s
        | s -> s in
      let uu____6345 = drop_irrel stack1 in
      match uu____6345 with
      | (App
          (uu____6348,
           {
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify);
             FStar_Syntax_Syntax.pos = uu____6349;
             FStar_Syntax_Syntax.vars = uu____6350;_},
           uu____6351, uu____6352))::uu____6353
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6358 -> false
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t, uu____6381) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t, uu____6391) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6412 ->
                  match uu____6412 with
                  | (a, uu____6422) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args) in
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6432 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6447 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6448 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6461 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6462 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6463 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6464 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6465 -> false
    | FStar_Syntax_Syntax.Tm_unknown -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6466 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6473 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6480 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6493 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6512 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6527 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6534 -> true
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6604 ->
                   match uu____6604 with
                   | (a, uu____6614) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____6625) ->
        ((maybe_weakly_reduced t1) ||
           (match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> maybe_weakly_reduced t2
            | FStar_Util.Inr c2 -> aux_comp c2))
          ||
          ((match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None -> false
            | FStar_Pervasives_Native.Some tac -> maybe_weakly_reduced tac))
    | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStar_Syntax_Syntax.Meta_pattern (uu____6720, args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____6775 ->
                        match uu____6775 with
                        | (a, uu____6785) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6794, uu____6795, t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6801, t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6807 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6814 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6815 -> false))
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_no -> true | uu____6821 -> false
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_yes -> true | uu____6827 -> false
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_fully -> true | uu____6833 -> false
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_reify -> true | uu____6839 -> false
let (should_unfold :
  FStar_TypeChecker_Cfg.cfg ->
    (FStar_TypeChecker_Cfg.cfg -> Prims.bool) ->
      FStar_Syntax_Syntax.fv ->
        FStar_TypeChecker_Env.qninfo -> should_unfold_res)
  =
  fun cfg ->
    fun should_reify1 ->
      fun fv ->
        fun qninfo ->
          let attrs =
            let uu____6868 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
            match uu____6868 with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some ats -> ats in
          let yes = (true, false, false) in
          let no = (false, false, false) in
          let fully = (true, true, false) in
          let reif = (true, false, true) in
          let yesno b = if b then yes else no in
          let fullyno b = if b then fully else no in
          let comb_or l =
            FStar_List.fold_right
              (fun uu____6996 ->
                 fun uu____6997 ->
                   match (uu____6996, uu____6997) with
                   | ((a, b, c), (x, y, z)) -> ((a || x), (b || y), (c || z)))
              l (false, false, false) in
          let string_of_res uu____7057 =
            match uu____7057 with
            | (x, y, z) ->
                let uu____7067 = FStar_Util.string_of_bool x in
                let uu____7068 = FStar_Util.string_of_bool y in
                let uu____7069 = FStar_Util.string_of_bool z in
                FStar_Util.format3 "(%s,%s,%s)" uu____7067 uu____7068
                  uu____7069 in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7088 ->
                    let uu____7089 = FStar_Syntax_Print.fv_to_string fv in
                    let uu____7090 = FStar_Util.string_of_bool b in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7089 uu____7090);
               if b then reif else no)
            else
              if
                (let uu____7098 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                 FStar_Option.isSome uu____7098)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7103 ->
                      FStar_Util.print_string
                        " >> It's a primop, not unfolding\n");
                 no)
              else
                (match (qninfo,
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr))
                 with
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec, uu____7137), uu____7138);
                        FStar_Syntax_Syntax.sigrng = uu____7139;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7141;
                        FStar_Syntax_Syntax.sigattrs = uu____7142;
                        FStar_Syntax_Syntax.sigopts = uu____7143;_},
                      uu____7144),
                     uu____7145),
                    uu____7146, uu____7147, uu____7148) when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7255 ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7256, uu____7257, uu____7258, uu____7259) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7326 ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec, uu____7328), uu____7329);
                        FStar_Syntax_Syntax.sigrng = uu____7330;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7332;
                        FStar_Syntax_Syntax.sigattrs = uu____7333;
                        FStar_Syntax_Syntax.sigopts = uu____7334;_},
                      uu____7335),
                     uu____7336),
                    uu____7337, uu____7338, uu____7339) when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7446 ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____7447, FStar_Pervasives_Native.Some uu____7448,
                    uu____7449, uu____7450) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7518 ->
                           let uu____7519 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7519);
                      (let uu____7520 =
                         let uu____7529 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7549 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____7549 in
                         let uu____7556 =
                           let uu____7565 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7585 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____7585 in
                           let uu____7596 =
                             let uu____7605 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7625 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____7625 in
                             [uu____7605] in
                           uu____7565 :: uu____7596 in
                         uu____7529 :: uu____7556 in
                       comb_or uu____7520))
                 | (uu____7656, uu____7657, FStar_Pervasives_Native.Some
                    uu____7658, uu____7659) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7727 ->
                           let uu____7728 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7728);
                      (let uu____7729 =
                         let uu____7738 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7758 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____7758 in
                         let uu____7765 =
                           let uu____7774 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7794 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____7794 in
                           let uu____7805 =
                             let uu____7814 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7834 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____7834 in
                             [uu____7814] in
                           uu____7774 :: uu____7805 in
                         uu____7738 :: uu____7765 in
                       comb_or uu____7729))
                 | (uu____7865, uu____7866, uu____7867,
                    FStar_Pervasives_Native.Some uu____7868) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7936 ->
                           let uu____7937 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7937);
                      (let uu____7938 =
                         let uu____7947 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7967 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____7967 in
                         let uu____7974 =
                           let uu____7983 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8003 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8003 in
                           let uu____8014 =
                             let uu____8023 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8043 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8043 in
                             [uu____8023] in
                           uu____7983 :: uu____8014 in
                         uu____7947 :: uu____7974 in
                       comb_or uu____7938))
                 | uu____8074 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8120 ->
                           let uu____8121 =
                             FStar_Syntax_Print.fv_to_string fv in
                           let uu____8122 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta in
                           let uu____8123 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8121 uu____8122 uu____8123);
                      (let uu____8124 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_8128 ->
                                 match uu___12_8128 with
                                 | FStar_TypeChecker_Env.NoDelta -> false
                                 | FStar_TypeChecker_Env.InliningDelta ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                     -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8130 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8130 l)) in
                       FStar_All.pipe_left yesno uu____8124))) in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8142 ->
               let uu____8143 = FStar_Syntax_Print.fv_to_string fv in
               let uu____8144 =
                 let uu____8145 = FStar_Syntax_Syntax.range_of_fv fv in
                 FStar_Range.string_of_range uu____8145 in
               let uu____8146 = string_of_res res in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8143 uu____8144 uu____8146);
          (match res with
           | (false, uu____8147, uu____8148) -> Should_unfold_no
           | (true, false, false) -> Should_unfold_yes
           | (true, true, false) -> Should_unfold_fully
           | (true, false, true) -> Should_unfold_reify
           | uu____8149 ->
               let uu____8156 =
                 let uu____8157 = string_of_res res in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____8157 in
               FStar_All.pipe_left failwith uu____8156)
let decide_unfolding :
  'uuuuuu8172 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu8172 ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list)
                  FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun rng ->
          fun fv ->
            fun qninfo ->
              let res =
                should_unfold cfg (fun cfg1 -> should_reify cfg1 stack1) fv
                  qninfo in
              match res with
              | Should_unfold_no -> FStar_Pervasives_Native.None
              | Should_unfold_yes ->
                  FStar_Pervasives_Native.Some (cfg, stack1)
              | Should_unfold_fully ->
                  let cfg' =
                    let uu___1168_8241 = cfg in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1170_8244 = cfg.FStar_TypeChecker_Cfg.steps in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.delta_constant);
                           FStar_TypeChecker_Cfg.unfold_only =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_fully =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_attr =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1170_8244.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1168_8241.FStar_TypeChecker_Cfg.reifying)
                    } in
                  let stack' =
                    match stack1 with
                    | (UnivArgs (us, r))::stack' -> (UnivArgs (us, r)) ::
                        (Cfg cfg) :: stack'
                    | stack' -> (Cfg cfg) :: stack' in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify ->
                  let rec push e s =
                    match s with
                    | [] -> [e]
                    | (UnivArgs (us, r))::t ->
                        let uu____8306 = push e t in (UnivArgs (us, r)) ::
                          uu____8306
                    | h::t -> e :: h :: t in
                  let ref =
                    let uu____8318 =
                      let uu____8319 =
                        let uu____8320 = FStar_Syntax_Syntax.lid_of_fv fv in
                        FStar_Const.Const_reflect uu____8320 in
                      FStar_Syntax_Syntax.Tm_constant uu____8319 in
                    FStar_Syntax_Syntax.mk uu____8318 FStar_Range.dummyRange in
                  let stack2 =
                    push
                      (App
                         (env1, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack1 in
                  FStar_Pervasives_Native.Some (cfg, stack2)
let (on_domain_lids : FStar_Ident.lident Prims.list) =
  let fext_lid s =
    FStar_Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s]
      FStar_Range.dummyRange in
  FStar_All.pipe_right ["on_domain"; "on_dom"; "on_domain_g"; "on_dom_g"]
    (FStar_List.map fext_lid)
let (is_fext_on_domain :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let is_on_dom fv =
      FStar_All.pipe_right on_domain_lids
        (FStar_List.existsb (fun l -> FStar_Syntax_Syntax.fv_eq_lid fv l)) in
    let uu____8363 =
      let uu____8364 = FStar_Syntax_Subst.compress t in
      uu____8364.FStar_Syntax_Syntax.n in
    match uu____8363 with
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu____8395 =
          let uu____8396 = FStar_Syntax_Util.un_uinst hd in
          uu____8396.FStar_Syntax_Syntax.n in
        (match uu____8395 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____8411 =
                 let uu____8418 =
                   let uu____8429 = FStar_All.pipe_right args FStar_List.tl in
                   FStar_All.pipe_right uu____8429 FStar_List.tl in
                 FStar_All.pipe_right uu____8418 FStar_List.hd in
               FStar_All.pipe_right uu____8411 FStar_Pervasives_Native.fst in
             FStar_Pervasives_Native.Some f
         | uu____8528 -> FStar_Pervasives_Native.None)
    | uu____8529 -> FStar_Pervasives_Native.None
let (is_partial_primop_app :
  FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun cfg ->
    fun t ->
      let uu____8540 = FStar_Syntax_Util.head_and_args t in
      match uu____8540 with
      | (hd, args) ->
          let uu____8583 =
            let uu____8584 = FStar_Syntax_Util.un_uinst hd in
            uu____8584.FStar_Syntax_Syntax.n in
          (match uu____8583 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____8588 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
               (match uu____8588 with
                | FStar_Pervasives_Native.Some prim_step ->
                    prim_step.FStar_TypeChecker_Cfg.arity >
                      (FStar_List.length args)
                | FStar_Pervasives_Native.None -> false)
           | uu____8600 -> false)
let rec (norm :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          let t1 =
            if
              (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____8877 ->
                   let uu____8892 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8892
               | uu____8893 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8902 ->
               let uu____8903 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____8904 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm in
               let uu____8905 = FStar_Syntax_Print.term_to_string t1 in
               let uu____8906 =
                 FStar_Util.string_of_int (FStar_List.length env1) in
               let uu____8913 =
                 let uu____8914 =
                   let uu____8917 = firstn (Prims.of_int (4)) stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8917 in
                 stack_to_string uu____8914 in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8903 uu____8904 uu____8905 uu____8906 uu____8913);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8943 ->
               let uu____8944 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8944);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8948 ->
                     let uu____8949 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8949);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8950 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8954 ->
                     let uu____8955 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8955);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____8956 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8960 ->
                     let uu____8961 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8961);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8962 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8966 ->
                     let uu____8967 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8967);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8968;
                 FStar_Syntax_Syntax.fv_delta = uu____8969;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8973 ->
                     let uu____8974 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8974);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8975;
                 FStar_Syntax_Syntax.fv_delta = uu____8976;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8977);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8987 ->
                     let uu____8988 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8988);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid in
               let uu____8992 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo in
               (match uu____8992 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____8995)
                    when uu____8995 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____8999 ->
                          let uu____9000 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9000);
                     rebuild cfg env1 stack1 t1)
                | uu____9001 ->
                    let uu____9004 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo in
                    (match uu____9004 with
                     | FStar_Pervasives_Native.Some (cfg1, stack2) ->
                         do_unfold_fv cfg1 env1 stack2 t1 qninfo fv
                     | FStar_Pervasives_Native.None ->
                         rebuild cfg env1 stack1 t1))
           | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
               let qi1 =
                 FStar_Syntax_Syntax.on_antiquoted (norm cfg env1 []) qi in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                   t1.FStar_Syntax_Syntax.pos in
               let uu____9043 = closure_as_term cfg env1 t2 in
               rebuild cfg env1 stack1 uu____9043
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9071 = is_norm_request hd args in
                  uu____9071 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9074 = rejig_norm_request hd args in
                 norm cfg env1 stack1 uu____9074))
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9102 = is_norm_request hd args in
                  uu____9102 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1292_9106 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1294_9109 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1294_9109.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1292_9106.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1292_9106.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1292_9106.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1292_9106.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1292_9106.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1292_9106.FStar_TypeChecker_Cfg.reifying)
                   } in
                 let uu____9114 =
                   get_norm_request cfg (norm cfg' env1 []) args in
                 match uu____9114 with
                 | FStar_Pervasives_Native.None ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____9147 ->
                                 fun stack2 ->
                                   match uu____9147 with
                                   | (a, aq) ->
                                       let uu____9159 =
                                         let uu____9160 =
                                           let uu____9167 =
                                             let uu____9168 =
                                               let uu____9199 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None in
                                               (env1, a, uu____9199, false) in
                                             Clos uu____9168 in
                                           (uu____9167, aq,
                                             (t1.FStar_Syntax_Syntax.pos)) in
                                         Arg uu____9160 in
                                       uu____9159 :: stack2) args) in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____9265 ->
                            let uu____9266 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____9266);
                       norm cfg env1 stack2 hd))
                 | FStar_Pervasives_Native.Some (s, tm) when is_nbe_request s
                     ->
                     let tm' = closure_as_term cfg env1 tm in
                     let start = FStar_Util.now () in
                     let tm_norm = nbe_eval cfg s tm' in
                     let fin = FStar_Util.now () in
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let cfg'1 =
                           FStar_TypeChecker_Cfg.config' [] s
                             cfg.FStar_TypeChecker_Cfg.tcenv in
                         let uu____9293 =
                           let uu____9294 =
                             let uu____9295 = FStar_Util.time_diff start fin in
                             FStar_Pervasives_Native.snd uu____9295 in
                           FStar_Util.string_of_int uu____9294 in
                         let uu____9300 =
                           FStar_Syntax_Print.term_to_string tm' in
                         let uu____9301 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1 in
                         let uu____9302 =
                           FStar_Syntax_Print.term_to_string tm_norm in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____9293 uu____9300 uu____9301 uu____9302)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s, tm) ->
                     let delta_level =
                       let uu____9319 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_9324 ->
                                 match uu___13_9324 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____9325 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____9326 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____9329 -> true
                                 | uu____9332 -> false)) in
                       if uu____9319
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta] in
                     let cfg'1 =
                       let uu___1332_9337 = cfg in
                       let uu____9338 =
                         let uu___1334_9339 =
                           FStar_TypeChecker_Cfg.to_fsteps s in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1334_9339.FStar_TypeChecker_Cfg.for_extraction)
                         } in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____9338;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1332_9337.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1332_9337.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1332_9337.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1332_9337.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1332_9337.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1332_9337.FStar_TypeChecker_Cfg.reifying)
                       } in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1 in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____9344 =
                           let uu____9345 =
                             let uu____9350 = FStar_Util.now () in
                             (tm, uu____9350) in
                           Debug uu____9345 in
                         uu____9344 :: tail
                       else tail in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u in
               let uu____9354 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____9354
           | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____9363 =
                      let uu____9370 =
                        FStar_List.map (norm_universe cfg env1) us in
                      (uu____9370, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____9363 in
                  let stack2 = us1 :: stack1 in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____9379 = lookup_bvar env1 x in
               (match uu____9379 with
                | Univ uu____9380 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos (env2, t0, r, fix) ->
                    if
                      ((Prims.op_Negation fix) ||
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                        ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full
                    then
                      let uu____9429 = FStar_ST.op_Bang r in
                      (match uu____9429 with
                       | FStar_Pervasives_Native.Some (env3, t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9512 ->
                                 let uu____9513 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____9514 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9513
                                   uu____9514);
                            (let uu____9515 = maybe_weakly_reduced t' in
                             if uu____9515
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____9516 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
               (match stack1 with
                | (UnivArgs uu____9558)::uu____9559 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c, uu____9569, uu____9570))::stack_rest ->
                    (match c with
                     | Univ uu____9574 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____9583 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9612 ->
                                    let uu____9613 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9613);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9647 ->
                                    let uu____9648 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9648);
                               (let body1 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env1) stack_rest body1))))
                | (Cfg cfg1)::stack2 -> norm cfg1 env1 stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo cfg r (env1, t1);
                     FStar_TypeChecker_Cfg.log cfg
                       (fun uu____9694 ->
                          let uu____9695 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9695);
                     norm cfg env1 stack2 t1)
                | (Match uu____9696)::uu____9697 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____9710 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____9710 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____9746 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____9789 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____9789)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_9796 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_9796.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_9796.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9797 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9803 ->
                                 let uu____9804 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9804);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_9815 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_9815.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____9818)::uu____9819 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____9828 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____9828 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____9864 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____9907 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____9907)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_9914 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_9914.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_9914.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9915 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9921 ->
                                 let uu____9922 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9922);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_9933 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_9933.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____9936)::uu____9937 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____9948 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____9948 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____9984 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10027 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10027)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10034 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10034.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10034.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10035 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10041 ->
                                 let uu____10042 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10042);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10053 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10053.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____10056)::uu____10057 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10070 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10070 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10106 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10149 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10149)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10156 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10156.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10156.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10157 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10163 ->
                                 let uu____10164 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10164);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10175 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10175.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____10178)::uu____10179 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10192 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10192 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10228 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10271 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10271)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10278 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10278.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10278.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10279 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10285 ->
                                 let uu____10286 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10286);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10297 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10297.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____10300)::uu____10301 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10314 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10314 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10350 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10393 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10393)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10400 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10400.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10400.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10401 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10407 ->
                                 let uu____10408 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10408);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10419 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10419.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____10422)::uu____10423 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10440 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10440 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10476 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10519 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10519)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10526 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10526.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10526.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10527 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10533 ->
                                 let uu____10534 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10534);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10545 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10545.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10550 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10550 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10586 -> dummy :: env2) env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu____10629 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10629)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10636 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10636.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10636.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10637 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10643 ->
                                 let uu____10644 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10644);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10655 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10655.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head, args) ->
               let strict_args =
                 let uu____10689 =
                   let uu____10690 = FStar_Syntax_Util.un_uinst head in
                   uu____10690.FStar_Syntax_Syntax.n in
                 match uu____10689 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____10698 -> FStar_Pervasives_Native.None in
               (match strict_args with
                | FStar_Pervasives_Native.None ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____10717 ->
                              fun stack2 ->
                                match uu____10717 with
                                | (a, aq) ->
                                    let uu____10729 =
                                      let uu____10730 =
                                        let uu____10737 =
                                          let uu____10738 =
                                            let uu____10769 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu____10769, false) in
                                          Clos uu____10738 in
                                        (uu____10737, aq,
                                          (t1.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____10730 in
                                    uu____10729 :: stack2) args) in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10835 ->
                          let uu____10836 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args) in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10836);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____10881 ->
                              match uu____10881 with
                              | (a, i) ->
                                  let uu____10892 = norm cfg env1 [] a in
                                  (uu____10892, i))) in
                    let norm_args_len = FStar_List.length norm_args in
                    let uu____10898 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____10904 = FStar_List.nth norm_args i in
                                 match uu____10904 with
                                 | (arg_i, uu____10914) ->
                                     let uu____10915 =
                                       FStar_Syntax_Util.head_and_args arg_i in
                                     (match uu____10915 with
                                      | (head1, uu____10933) ->
                                          let uu____10958 =
                                            let uu____10959 =
                                              FStar_Syntax_Util.un_uinst
                                                head1 in
                                            uu____10959.FStar_Syntax_Syntax.n in
                                          (match uu____10958 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____10962 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____10964 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____10964
                                           | uu____10965 -> false))))) in
                    if uu____10898
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____10980 ->
                                fun stack2 ->
                                  match uu____10980 with
                                  | (a, aq) ->
                                      let uu____10992 =
                                        let uu____10993 =
                                          let uu____11000 =
                                            let uu____11001 =
                                              let uu____11032 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a)) in
                                              (env1, a, uu____11032, false) in
                                            Clos uu____11001 in
                                          (uu____11000, aq,
                                            (t1.FStar_Syntax_Syntax.pos)) in
                                        Arg uu____10993 in
                                      uu____10992 :: stack2) norm_args) in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____11112 ->
                            let uu____11113 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____11113);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x, uu____11126) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
               -> norm cfg env1 stack1 x.FStar_Syntax_Syntax.sort
           | FStar_Syntax_Syntax.Tm_refine (x, f) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 (match (env1, stack1) with
                  | ([], []) ->
                      let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___1525_11170 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1525_11170.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1525_11170.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2
                  | uu____11171 ->
                      let uu____11186 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 uu____11186)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
                  let uu____11189 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____11189 with
                  | (closing, f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1 in
                      let t2 =
                        let uu____11220 =
                          let uu____11221 =
                            let uu____11228 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___1534_11234 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1534_11234.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1534_11234.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11228) in
                          FStar_Syntax_Syntax.Tm_refine uu____11221 in
                        FStar_Syntax_Syntax.mk uu____11220
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____11257 = closure_as_term cfg env1 t1 in
                 rebuild cfg env1 stack1 uu____11257
               else
                 (let uu____11259 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____11259 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu____11267 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2 -> fun uu____11293 -> dummy :: env2)
                               env1) in
                        norm_comp cfg uu____11267 c1 in
                      let t2 =
                        let uu____11317 = norm_binders cfg env1 bs1 in
                        FStar_Syntax_Util.arrow uu____11317 c2 in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) ->
               (match stack1 with
                | (Match uu____11430)::uu____11431 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11444 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____11445)::uu____11446 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11457 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____11458,
                     {
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify);
                       FStar_Syntax_Syntax.pos = uu____11459;
                       FStar_Syntax_Syntax.vars = uu____11460;_},
                     uu____11461, uu____11462))::uu____11463
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11470 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____11471)::uu____11472 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11483 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____11484 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11487 ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11 in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____11491 ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11516 = norm cfg env1 [] t2 in
                             FStar_Util.Inl uu____11516
                         | FStar_Util.Inr c ->
                             let uu____11530 = norm_comp cfg env1 c in
                             FStar_Util.Inr uu____11530 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 []) in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____11553 =
                               let uu____11554 =
                                 let uu____11581 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____11581, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11554 in
                             FStar_Syntax_Syntax.mk uu____11553
                               t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env1 stack2 t2
                       | uu____11616 ->
                           let uu____11617 =
                             let uu____11618 =
                               let uu____11619 =
                                 let uu____11646 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____11646, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11619 in
                             FStar_Syntax_Syntax.mk uu____11618
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env1 stack1 uu____11617))))
           | FStar_Syntax_Syntax.Tm_match (head, branches1) ->
               let stack2 =
                 (Match (env1, branches1, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack1 in
               if
                 ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                   &&
                   (Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak)
               then
                 let cfg' =
                   let uu___1613_11723 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1615_11726 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1615_11726.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1613_11723.FStar_TypeChecker_Cfg.reifying)
                   } in
                 norm cfg' env1 ((Cfg cfg) :: stack2) head
               else norm cfg env1 stack2 head
           | FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb ->
                         let uu____11762 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____11762 with
                         | (openings, lbunivs) ->
                             let cfg1 =
                               let uu___1628_11782 = cfg in
                               let uu____11783 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____11783;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1628_11782.FStar_TypeChecker_Cfg.reifying)
                               } in
                             let norm1 t2 =
                               let uu____11790 =
                                 let uu____11791 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env1 [] uu____11791 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11790 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___1635_11794 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1635_11794.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1635_11794.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1635_11794.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1635_11794.FStar_Syntax_Syntax.lbpos)
                             })) in
               let uu____11795 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____11795
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11806,
                 { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____11807;
                   FStar_Syntax_Syntax.lbunivs = uu____11808;
                   FStar_Syntax_Syntax.lbtyp = uu____11809;
                   FStar_Syntax_Syntax.lbeff = uu____11810;
                   FStar_Syntax_Syntax.lbdef = uu____11811;
                   FStar_Syntax_Syntax.lbattrs = uu____11812;
                   FStar_Syntax_Syntax.lbpos = uu____11813;_}::uu____11814),
                uu____11815)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
               let uu____11854 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb in
               if uu____11854
               then
                 let binder =
                   let uu____11856 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____11856 in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef in
                 let env2 =
                   let uu____11867 =
                     let uu____11874 =
                       let uu____11875 =
                         let uu____11906 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env1, def, uu____11906, false) in
                       Clos uu____11875 in
                     ((FStar_Pervasives_Native.Some binder), uu____11874) in
                   uu____11867 :: env1 in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11979 ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____11981 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____11983 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff in
                       FStar_Syntax_Util.is_div_effect uu____11983) in
                  if uu____11981
                  then
                    let ffun =
                      let uu____11987 =
                        let uu____11988 =
                          let uu____12007 =
                            let uu____12016 =
                              let uu____12023 =
                                FStar_All.pipe_right
                                  lb.FStar_Syntax_Syntax.lbname
                                  FStar_Util.left in
                              FStar_Syntax_Syntax.mk_binder uu____12023 in
                            [uu____12016] in
                          (uu____12007, body, FStar_Pervasives_Native.None) in
                        FStar_Syntax_Syntax.Tm_abs uu____11988 in
                      FStar_Syntax_Syntax.mk uu____11987
                        t1.FStar_Syntax_Syntax.pos in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12057 ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12061 ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____12062 = closure_as_term cfg env1 t1 in
                        rebuild cfg env1 stack1 uu____12062))
                    else
                      (let uu____12064 =
                         let uu____12069 =
                           let uu____12070 =
                             let uu____12077 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left in
                             FStar_All.pipe_right uu____12077
                               FStar_Syntax_Syntax.mk_binder in
                           [uu____12070] in
                         FStar_Syntax_Subst.open_term uu____12069 body in
                       match uu____12064 with
                       | (bs, body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____12104 ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                             let lbname =
                               let x =
                                 let uu____12112 = FStar_List.hd bs in
                                 FStar_Pervasives_Native.fst uu____12112 in
                               FStar_Util.Inl
                                 (let uu___1682_12128 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1682_12128.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1682_12128.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }) in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____12131 ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1687_12133 = lb in
                                let uu____12134 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef in
                                let uu____12137 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1687_12133.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1687_12133.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____12134;
                                  FStar_Syntax_Syntax.lbattrs = uu____12137;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1687_12133.FStar_Syntax_Syntax.lbpos)
                                } in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2 ->
                                        fun uu____12172 -> dummy :: env2)
                                     env1) in
                              let stack2 = (Cfg cfg) :: stack1 in
                              let cfg1 =
                                let uu___1694_12197 = cfg in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1694_12197.FStar_TypeChecker_Cfg.reifying)
                                } in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____12200 ->
                                   FStar_Util.print_string
                                     "+++ Normalizing Tm_let -- body\n");
                              norm cfg1 env'
                                ((Let
                                    (env1, bs, lb1,
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack2) body1)))))
           | FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                 ||
                 (((Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     &&
                     (Prims.op_Negation
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full))
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)
               ->
               let uu____12217 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12217 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12253 =
                               let uu___1710_12254 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1710_12254.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1710_12254.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12253 in
                           let uu____12255 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12255 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env1 xs in
                               let env2 =
                                 let uu____12281 =
                                   FStar_List.map (fun uu____12303 -> dummy)
                                     xs1 in
                                 let uu____12310 =
                                   let uu____12319 =
                                     FStar_List.map
                                       (fun uu____12335 -> dummy) lbs1 in
                                   FStar_List.append uu____12319 env1 in
                                 FStar_List.append uu____12281 uu____12310 in
                               let def_body1 = norm cfg env2 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12355 =
                                       let uu___1724_12356 = rc in
                                       let uu____12357 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1724_12356.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12357;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1724_12356.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12355
                                 | uu____12366 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___1729_12372 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1729_12372.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1729_12372.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1729_12372.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1729_12372.FStar_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu____12382 =
                        FStar_List.map (fun uu____12398 -> dummy) lbs2 in
                      FStar_List.append uu____12382 env1 in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12406 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12406 with
                     | (lbs3, body3) ->
                         let t2 =
                           let uu___1738_12422 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1738_12422.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1738_12422.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs, body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____12451 = closure_as_term cfg env1 t1 in
               rebuild cfg env1 stack1 uu____12451
           | FStar_Syntax_Syntax.Tm_let (lbs, body) ->
               let uu____12470 =
                 FStar_List.fold_right
                   (fun lb ->
                      fun uu____12546 ->
                        match uu____12546 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___1754_12667 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1754_12667.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1754_12667.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env1, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos), (i + Prims.int_one)))
                   (FStar_Pervasives_Native.snd lbs)
                   (env1, [], Prims.int_zero) in
               (match uu____12470 with
                | (rec_env, memos, uu____12850) ->
                    let uu____12903 =
                      FStar_List.map2
                        (fun lb ->
                           fun memo ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb ->
                           fun env2 ->
                             let uu____13086 =
                               let uu____13093 =
                                 let uu____13094 =
                                   let uu____13125 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13125, false) in
                                 Clos uu____13094 in
                               (FStar_Pervasives_Native.None, uu____13093) in
                             uu____13086 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1 in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head, m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____13207 ->
                     let uu____13208 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13208);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1, t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13230 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____13232::uu____13233 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l, r, uu____13238) ->
                                 norm cfg env1 ((Meta (env1, m, r)) ::
                                   stack1) head
                             | FStar_Syntax_Syntax.Meta_pattern (names, args)
                                 ->
                                 let args1 = norm_pattern_args cfg env1 args in
                                 let names1 =
                                   FStar_All.pipe_right names
                                     (FStar_List.map (norm cfg env1 [])) in
                                 norm cfg env1
                                   ((Meta
                                       (env1,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (names1, args1)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack1) head
                             | uu____13313 -> norm cfg env1 stack1 head)
                        | [] ->
                            let head1 = norm cfg env1 [] head in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names, args) ->
                                  let names1 =
                                    FStar_All.pipe_right names
                                      (FStar_List.map (norm cfg env1 [])) in
                                  let uu____13361 =
                                    let uu____13382 =
                                      norm_pattern_args cfg env1 args in
                                    (names1, uu____13382) in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13361
                              | uu____13411 -> m in
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13417 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13433 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13447 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____13460 =
                        let uu____13461 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____13462 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13461 uu____13462 in
                      failwith uu____13460
                    else
                      (let uu____13464 = inline_closure_env cfg env1 [] t2 in
                       rebuild cfg env1 stack1 uu____13464)
                | uu____13465 -> norm cfg env1 stack1 t2))
and (do_unfold_fv :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t0 ->
          fun qninfo ->
            fun f ->
              let uu____13474 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu____13474 with
              | FStar_Pervasives_Native.None ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____13488 ->
                        let uu____13489 = FStar_Syntax_Print.fv_to_string f in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____13489);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us, t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____13500 ->
                        let uu____13501 =
                          FStar_Syntax_Print.term_to_string t0 in
                        let uu____13502 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____13501 uu____13502);
                   (let t1 =
                      if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_until
                          =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          t0.FStar_Syntax_Syntax.pos t in
                    let n = FStar_List.length us in
                    if n > Prims.int_zero
                    then
                      match stack1 with
                      | (UnivArgs (us', uu____13509))::stack2 ->
                          ((let uu____13518 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm") in
                            if uu____13518
                            then
                              FStar_List.iter
                                (fun x ->
                                   let uu____13522 =
                                     FStar_Syntax_Print.univ_to_string x in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____13522) us'
                            else ());
                           (let env2 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env2 ->
                                      fun u ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env2) env1) in
                            norm cfg env2 stack2 t1))
                      | uu____13555 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____13558 ->
                          let uu____13561 =
                            let uu____13562 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13562 in
                          failwith uu____13561
                    else norm cfg env1 stack1 t1))
and (reduce_impure_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,
            (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name))
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun head ->
          fun m ->
            fun t ->
              let t1 = norm cfg env1 [] t in
              let uu____13579 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                then
                  let new_steps =
                    [FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.AllowUnboundUniverses;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.Inlining] in
                  let cfg' =
                    let uu___1865_13596 = cfg in
                    let uu____13597 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____13597;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1865_13596.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1865_13596.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1865_13596.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1865_13596.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1865_13596.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1865_13596.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1865_13596.FStar_TypeChecker_Cfg.reifying)
                    } in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1) in
              match uu____13579 with
              | (cfg1, stack2) ->
                  let metadata =
                    match m with
                    | FStar_Util.Inl m1 ->
                        FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                    | FStar_Util.Inr (m1, m') ->
                        FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
                  norm cfg1 env1
                    ((Meta (env1, metadata, (head.FStar_Syntax_Syntax.pos)))
                    :: stack2) head
and (do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback ->
    fun cfg ->
      fun env1 ->
        fun stack1 ->
          fun top ->
            fun m ->
              fun t ->
                (match stack1 with
                 | (App
                     (uu____13637,
                      {
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify);
                        FStar_Syntax_Syntax.pos = uu____13638;
                        FStar_Syntax_Syntax.vars = uu____13639;_},
                      uu____13640, uu____13641))::uu____13642
                     -> ()
                 | uu____13647 ->
                     let uu____13650 =
                       let uu____13651 = stack_to_string stack1 in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____13651 in
                     failwith uu____13650);
                (let top0 = top in
                 let top1 = FStar_Syntax_Util.unascribe top in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____13658 ->
                      let uu____13659 = FStar_Syntax_Print.tag_of_term top1 in
                      let uu____13660 =
                        FStar_Syntax_Print.term_to_string top1 in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____13659
                        uu____13660);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1 in
                  let uu____13662 =
                    let uu____13663 = FStar_Syntax_Subst.compress top2 in
                    uu____13663.FStar_Syntax_Syntax.n in
                  match uu____13662 with
                  | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name in
                      let uu____13682 =
                        let uu____13691 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr in
                        FStar_All.pipe_right uu____13691 FStar_Util.must in
                      (match uu____13682 with
                       | (uu____13706, repr) ->
                           let uu____13716 =
                             let uu____13723 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr in
                             FStar_All.pipe_right uu____13723 FStar_Util.must in
                           (match uu____13716 with
                            | (uu____13760, bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____13766 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____13776 =
                                         let uu____13777 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____13777.FStar_Syntax_Syntax.n in
                                       match uu____13776 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,
                                            FStar_Syntax_Syntax.Meta_monadic
                                            (uu____13783, uu____13784))
                                           ->
                                           let uu____13793 =
                                             let uu____13794 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____13794.FStar_Syntax_Syntax.n in
                                           (match uu____13793 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,
                                                 FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____13800, msrc,
                                                  uu____13802))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____13811 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13811
                                            | uu____13812 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____13813 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____13814 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____13814 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1944_13819 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1944_13819.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1944_13819.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1944_13819.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1944_13819.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1944_13819.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let uu____13820 =
                                            FStar_List.tl stack1 in
                                          let uu____13821 =
                                            let uu____13822 =
                                              let uu____13823 =
                                                let uu____13836 =
                                                  FStar_Syntax_Util.mk_reify
                                                    body in
                                                ((false, [lb1]), uu____13836) in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu____13823 in
                                            FStar_Syntax_Syntax.mk
                                              uu____13822
                                              top2.FStar_Syntax_Syntax.pos in
                                          norm cfg env1 uu____13820
                                            uu____13821
                                      | FStar_Pervasives_Native.None ->
                                          let uu____13849 =
                                            let uu____13850 = is_return body in
                                            match uu____13850 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____13854;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____13855;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____13858 -> false in
                                          if uu____13849
                                          then
                                            norm cfg env1 stack1
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let rng =
                                               top2.FStar_Syntax_Syntax.pos in
                                             let head =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef in
                                             let body1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body in
                                             let body_rc =
                                               {
                                                 FStar_Syntax_Syntax.residual_effect
                                                   = m;
                                                 FStar_Syntax_Syntax.residual_typ
                                                   =
                                                   (FStar_Pervasives_Native.Some
                                                      t);
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               } in
                                             let body2 =
                                               let uu____13883 =
                                                 let uu____13884 =
                                                   let uu____13903 =
                                                     let uu____13912 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         x in
                                                     [uu____13912] in
                                                   (uu____13903, body1,
                                                     (FStar_Pervasives_Native.Some
                                                        body_rc)) in
                                                 FStar_Syntax_Syntax.Tm_abs
                                                   uu____13884 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13883
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close =
                                               closure_as_term cfg env1 in
                                             let bind_inst =
                                               let uu____13951 =
                                                 let uu____13952 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____13952.FStar_Syntax_Syntax.n in
                                               match uu____13951 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind,
                                                    uu____13958::uu____13959::[])
                                                   ->
                                                   let uu____13964 =
                                                     let uu____13965 =
                                                       let uu____13972 =
                                                         let uu____13973 =
                                                           let uu____13974 =
                                                             close
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.FStar_TypeChecker_Cfg.tcenv
                                                             uu____13974 in
                                                         let uu____13975 =
                                                           let uu____13978 =
                                                             let uu____13979
                                                               = close t in
                                                             (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.FStar_TypeChecker_Cfg.tcenv
                                                               uu____13979 in
                                                           [uu____13978] in
                                                         uu____13973 ::
                                                           uu____13975 in
                                                       (bind, uu____13972) in
                                                     FStar_Syntax_Syntax.Tm_uinst
                                                       uu____13965 in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____13964 rng
                                               | uu____13982 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let bind_inst_args f_arg =
                                               let uu____13993 =
                                                 FStar_Syntax_Util.is_layered
                                                   ed in
                                               if uu____13993
                                               then
                                                 let unit_args =
                                                   let uu____13999 =
                                                     let uu____14000 =
                                                       let uu____14003 =
                                                         let uu____14004 =
                                                           FStar_All.pipe_right
                                                             ed
                                                             FStar_Syntax_Util.get_bind_vc_combinator in
                                                         FStar_All.pipe_right
                                                           uu____14004
                                                           FStar_Pervasives_Native.snd in
                                                       FStar_All.pipe_right
                                                         uu____14003
                                                         FStar_Syntax_Subst.compress in
                                                     uu____14000.FStar_Syntax_Syntax.n in
                                                   match uu____13999 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (uu____14037::uu____14038::bs,
                                                        uu____14040)
                                                       when
                                                       (FStar_List.length bs)
                                                         >=
                                                         (Prims.of_int (2))
                                                       ->
                                                       let uu____14091 =
                                                         let uu____14100 =
                                                           FStar_All.pipe_right
                                                             bs
                                                             (FStar_List.splitAt
                                                                ((FStar_List.length
                                                                    bs)
                                                                   -
                                                                   (Prims.of_int (2)))) in
                                                         FStar_All.pipe_right
                                                           uu____14100
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____14091
                                                         (FStar_List.map
                                                            (fun uu____14222
                                                               ->
                                                               FStar_Syntax_Syntax.as_arg
                                                                 FStar_Syntax_Syntax.unit_const))
                                                   | uu____14229 ->
                                                       let uu____14230 =
                                                         let uu____14235 =
                                                           let uu____14236 =
                                                             FStar_Ident.string_of_lid
                                                               ed.FStar_Syntax_Syntax.mname in
                                                           let uu____14237 =
                                                             let uu____14238
                                                               =
                                                               let uu____14239
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator in
                                                               FStar_All.pipe_right
                                                                 uu____14239
                                                                 FStar_Pervasives_Native.snd in
                                                             FStar_All.pipe_right
                                                               uu____14238
                                                               FStar_Syntax_Print.term_to_string in
                                                           FStar_Util.format2
                                                             "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                             uu____14236
                                                             uu____14237 in
                                                         (FStar_Errors.Fatal_UnexpectedEffect,
                                                           uu____14235) in
                                                       FStar_Errors.raise_error
                                                         uu____14230 rng in
                                                 let uu____14262 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____14263 =
                                                   let uu____14266 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____14267 =
                                                     let uu____14270 =
                                                       let uu____14273 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           f_arg in
                                                       let uu____14274 =
                                                         let uu____14277 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2 in
                                                         [uu____14277] in
                                                       uu____14273 ::
                                                         uu____14274 in
                                                     FStar_List.append
                                                       unit_args uu____14270 in
                                                   uu____14266 :: uu____14267 in
                                                 uu____14262 :: uu____14263
                                               else
                                                 (let maybe_range_arg =
                                                    let uu____14282 =
                                                      FStar_Util.for_some
                                                        (FStar_Syntax_Util.attr_eq
                                                           FStar_Syntax_Util.dm4f_bind_range_attr)
                                                        ed.FStar_Syntax_Syntax.eff_attrs in
                                                    if uu____14282
                                                    then
                                                      let uu____14285 =
                                                        let uu____14286 =
                                                          FStar_TypeChecker_Cfg.embed_simple
                                                            FStar_Syntax_Embeddings.e_range
                                                            lb.FStar_Syntax_Syntax.lbpos
                                                            lb.FStar_Syntax_Syntax.lbpos in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____14286 in
                                                      let uu____14287 =
                                                        let uu____14290 =
                                                          let uu____14291 =
                                                            FStar_TypeChecker_Cfg.embed_simple
                                                              FStar_Syntax_Embeddings.e_range
                                                              body2.FStar_Syntax_Syntax.pos
                                                              body2.FStar_Syntax_Syntax.pos in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu____14291 in
                                                        [uu____14290] in
                                                      uu____14285 ::
                                                        uu____14287
                                                    else [] in
                                                  let uu____14293 =
                                                    let uu____14296 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp in
                                                    let uu____14297 =
                                                      let uu____14300 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t in
                                                      [uu____14300] in
                                                    uu____14296 ::
                                                      uu____14297 in
                                                  let uu____14301 =
                                                    let uu____14304 =
                                                      let uu____14307 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun in
                                                      let uu____14308 =
                                                        let uu____14311 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            f_arg in
                                                        let uu____14312 =
                                                          let uu____14315 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu____14316 =
                                                            let uu____14319 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2 in
                                                            [uu____14319] in
                                                          uu____14315 ::
                                                            uu____14316 in
                                                        uu____14311 ::
                                                          uu____14312 in
                                                      uu____14307 ::
                                                        uu____14308 in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____14304 in
                                                  FStar_List.append
                                                    uu____14293 uu____14301) in
                                             let reified =
                                               let is_total_effect =
                                                 FStar_TypeChecker_Env.is_total_effect
                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                   eff_name in
                                               if is_total_effect
                                               then
                                                 let uu____14322 =
                                                   let uu____14323 =
                                                     let uu____14340 =
                                                       bind_inst_args head in
                                                     (bind_inst, uu____14340) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14323 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14322 rng
                                               else
                                                 (let uu____14364 =
                                                    let bv =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        x.FStar_Syntax_Syntax.sort in
                                                    let lb1 =
                                                      let uu____14373 =
                                                        let uu____14376 =
                                                          let uu____14387 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              x.FStar_Syntax_Syntax.sort in
                                                          [uu____14387] in
                                                        FStar_Syntax_Util.mk_app
                                                          repr uu____14376 in
                                                      {
                                                        FStar_Syntax_Syntax.lbname
                                                          =
                                                          (FStar_Util.Inl bv);
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = [];
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____14373;
                                                        FStar_Syntax_Syntax.lbeff
                                                          =
                                                          (if is_total_effect
                                                           then
                                                             FStar_Parser_Const.effect_Tot_lid
                                                           else
                                                             FStar_Parser_Const.effect_Dv_lid);
                                                        FStar_Syntax_Syntax.lbdef
                                                          = head;
                                                        FStar_Syntax_Syntax.lbattrs
                                                          = [];
                                                        FStar_Syntax_Syntax.lbpos
                                                          =
                                                          (head.FStar_Syntax_Syntax.pos)
                                                      } in
                                                    let uu____14415 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        bv in
                                                    (lb1, bv, uu____14415) in
                                                  match uu____14364 with
                                                  | (lb_head, head_bv, head1)
                                                      ->
                                                      let uu____14419 =
                                                        let uu____14420 =
                                                          let uu____14433 =
                                                            let uu____14436 =
                                                              let uu____14443
                                                                =
                                                                let uu____14444
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    head_bv in
                                                                [uu____14444] in
                                                              FStar_Syntax_Subst.close
                                                                uu____14443 in
                                                            let uu____14463 =
                                                              let uu____14464
                                                                =
                                                                let uu____14465
                                                                  =
                                                                  let uu____14482
                                                                    =
                                                                    bind_inst_args
                                                                    head1 in
                                                                  (bind_inst,
                                                                    uu____14482) in
                                                                FStar_Syntax_Syntax.Tm_app
                                                                  uu____14465 in
                                                              FStar_Syntax_Syntax.mk
                                                                uu____14464
                                                                rng in
                                                            FStar_All.pipe_left
                                                              uu____14436
                                                              uu____14463 in
                                                          ((false, [lb_head]),
                                                            uu____14433) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____14420 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____14419 rng) in
                                             FStar_TypeChecker_Cfg.log cfg
                                               (fun uu____14521 ->
                                                  let uu____14522 =
                                                    FStar_Syntax_Print.term_to_string
                                                      top0 in
                                                  let uu____14523 =
                                                    FStar_Syntax_Print.term_to_string
                                                      reified in
                                                  FStar_Util.print2
                                                    "Reified (1) <%s> to %s\n"
                                                    uu____14522 uu____14523);
                                             (let uu____14524 =
                                                FStar_List.tl stack1 in
                                              norm cfg env1 uu____14524
                                                reified))))))
                  | FStar_Syntax_Syntax.Tm_app (head, args) ->
                      ((let uu____14552 = FStar_Options.defensive () in
                        if uu____14552
                        then
                          let is_arg_impure uu____14564 =
                            match uu____14564 with
                            | (e, q) ->
                                let uu____14577 =
                                  let uu____14578 =
                                    FStar_Syntax_Subst.compress e in
                                  uu____14578.FStar_Syntax_Syntax.n in
                                (match uu____14577 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,
                                      FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1, m2, t'))
                                     ->
                                     let uu____14593 =
                                       FStar_Syntax_Util.is_pure_effect m1 in
                                     Prims.op_Negation uu____14593
                                 | uu____14594 -> false) in
                          let uu____14595 =
                            let uu____14596 =
                              let uu____14607 =
                                FStar_Syntax_Syntax.as_arg head in
                              uu____14607 :: args in
                            FStar_Util.for_some is_arg_impure uu____14596 in
                          (if uu____14595
                           then
                             let uu____14632 =
                               let uu____14637 =
                                 let uu____14638 =
                                   FStar_Syntax_Print.term_to_string top2 in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____14638 in
                               (FStar_Errors.Warning_Defensive, uu____14637) in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____14632
                           else ())
                        else ());
                       (let fallback1 uu____14646 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____14650 ->
                               let uu____14651 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____14651 "");
                          (let uu____14652 = FStar_List.tl stack1 in
                           let uu____14653 = FStar_Syntax_Util.mk_reify top2 in
                           norm cfg env1 uu____14652 uu____14653) in
                        let fallback2 uu____14659 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____14663 ->
                               let uu____14664 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____14664 "");
                          (let uu____14665 = FStar_List.tl stack1 in
                           let uu____14666 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos in
                           norm cfg env1 uu____14665 uu____14666) in
                        let uu____14671 =
                          let uu____14672 = FStar_Syntax_Util.un_uinst head in
                          uu____14672.FStar_Syntax_Syntax.n in
                        match uu____14671 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid in
                            let uu____14678 =
                              let uu____14679 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid in
                              Prims.op_Negation uu____14679 in
                            if uu____14678
                            then fallback1 ()
                            else
                              (let uu____14681 =
                                 let uu____14682 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isNone uu____14682 in
                               if uu____14681
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____14695 =
                                      FStar_Syntax_Util.mk_reify head in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____14695
                                      args t.FStar_Syntax_Syntax.pos in
                                  let uu____14696 = FStar_List.tl stack1 in
                                  norm cfg env1 uu____14696 t1))
                        | uu____14697 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic uu____14699) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, t'))
                      ->
                      let lifted =
                        let uu____14723 = closure_as_term cfg env1 t' in
                        reify_lift cfg e msrc mtgt uu____14723 in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____14727 ->
                            let uu____14728 =
                              FStar_Syntax_Print.term_to_string lifted in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____14728);
                       (let uu____14729 = FStar_List.tl stack1 in
                        norm cfg env1 uu____14729 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e, branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____14850 ->
                                match uu____14850 with
                                | (pat, wopt, tm) ->
                                    let uu____14898 =
                                      FStar_Syntax_Util.mk_reify tm in
                                    (pat, wopt, uu____14898))) in
                      let tm =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos in
                      let uu____14930 = FStar_List.tl stack1 in
                      norm cfg env1 uu____14930 tm
                  | uu____14931 -> fallback ()))
and (reify_lift :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun e ->
      fun msrc ->
        fun mtgt ->
          fun t ->
            let env1 = cfg.FStar_TypeChecker_Cfg.tcenv in
            FStar_TypeChecker_Cfg.log cfg
              (fun uu____14945 ->
                 let uu____14946 = FStar_Ident.string_of_lid msrc in
                 let uu____14947 = FStar_Ident.string_of_lid mtgt in
                 let uu____14948 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14946
                   uu____14947 uu____14948);
            (let uu____14949 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____14951 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1) in
                  Prims.op_Negation uu____14951) in
             if uu____14949
             then
               let ed =
                 let uu____14953 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____14953 in
               let uu____14954 =
                 let uu____14963 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 FStar_All.pipe_right uu____14963 FStar_Util.must in
               match uu____14954 with
               | (uu____15010, repr) ->
                   let uu____15020 =
                     let uu____15029 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr in
                     FStar_All.pipe_right uu____15029 FStar_Util.must in
                   (match uu____15020 with
                    | (uu____15076, return_repr) ->
                        let return_inst =
                          let uu____15089 =
                            let uu____15090 =
                              FStar_Syntax_Subst.compress return_repr in
                            uu____15090.FStar_Syntax_Syntax.n in
                          match uu____15089 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm, uu____15096::[]) ->
                              let uu____15101 =
                                let uu____15102 =
                                  let uu____15109 =
                                    let uu____15110 =
                                      env1.FStar_TypeChecker_Env.universe_of
                                        env1 t in
                                    [uu____15110] in
                                  (return_tm, uu____15109) in
                                FStar_Syntax_Syntax.Tm_uinst uu____15102 in
                              FStar_Syntax_Syntax.mk uu____15101
                                e.FStar_Syntax_Syntax.pos
                          | uu____15113 ->
                              failwith "NIY : Reification of indexed effects" in
                        let uu____15116 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t in
                          let lb =
                            let uu____15127 =
                              let uu____15130 =
                                let uu____15141 =
                                  FStar_Syntax_Syntax.as_arg t in
                                [uu____15141] in
                              FStar_Syntax_Util.mk_app repr uu____15130 in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____15127;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            } in
                          let uu____15168 = FStar_Syntax_Syntax.bv_to_name bv in
                          (lb, bv, uu____15168) in
                        (match uu____15116 with
                         | (lb_e, e_bv, e1) ->
                             let uu____15180 =
                               let uu____15181 =
                                 let uu____15194 =
                                   let uu____15197 =
                                     let uu____15204 =
                                       let uu____15205 =
                                         FStar_Syntax_Syntax.mk_binder e_bv in
                                       [uu____15205] in
                                     FStar_Syntax_Subst.close uu____15204 in
                                   let uu____15224 =
                                     let uu____15225 =
                                       let uu____15226 =
                                         let uu____15243 =
                                           let uu____15254 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____15263 =
                                             let uu____15274 =
                                               FStar_Syntax_Syntax.as_arg e1 in
                                             [uu____15274] in
                                           uu____15254 :: uu____15263 in
                                         (return_inst, uu____15243) in
                                       FStar_Syntax_Syntax.Tm_app uu____15226 in
                                     FStar_Syntax_Syntax.mk uu____15225
                                       e1.FStar_Syntax_Syntax.pos in
                                   FStar_All.pipe_left uu____15197
                                     uu____15224 in
                                 ((false, [lb_e]), uu____15194) in
                               FStar_Syntax_Syntax.Tm_let uu____15181 in
                             FStar_Syntax_Syntax.mk uu____15180
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____15332 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt in
                match uu____15332 with
                | FStar_Pervasives_Native.None ->
                    let uu____15335 =
                      let uu____15336 = FStar_Ident.string_of_lid msrc in
                      let uu____15337 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15336 uu____15337 in
                    failwith uu____15335
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15338;
                      FStar_TypeChecker_Env.mtarget = uu____15339;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15340;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None;_};_}
                    ->
                    let uu____15360 =
                      let uu____15361 = FStar_Ident.string_of_lid msrc in
                      let uu____15362 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15361 uu____15362 in
                    failwith uu____15360
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15363;
                      FStar_TypeChecker_Env.mtarget = uu____15364;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15365;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____15396 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc in
                      if uu____15396
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____15398 =
                           let uu____15399 =
                             let uu____15418 =
                               let uu____15427 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_Syntax_Syntax.t_unit in
                               [uu____15427] in
                             (uu____15418, e,
                               (FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      msrc;
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t);
                                    FStar_Syntax_Syntax.residual_flags = []
                                  })) in
                           FStar_Syntax_Syntax.Tm_abs uu____15399 in
                         FStar_Syntax_Syntax.mk uu____15398
                           e.FStar_Syntax_Syntax.pos) in
                    let uu____15460 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t in
                    lift uu____15460 t e1))
and (norm_pattern_args :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          Prims.list Prims.list)
  =
  fun cfg ->
    fun env1 ->
      fun args ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____15530 ->
                   match uu____15530 with
                   | (a, imp) ->
                       let uu____15549 = norm cfg env1 [] a in
                       (uu____15549, imp))))
and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg ->
    fun env1 ->
      fun comp ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____15559 ->
             let uu____15560 = FStar_Syntax_Print.comp_to_string comp in
             let uu____15561 =
               FStar_Util.string_of_int (FStar_List.length env1) in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____15560 uu____15561);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15585 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____15588 ->
                        FStar_Pervasives_Native.Some uu____15588) uu____15585
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2128_15589 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2128_15589.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2128_15589.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15611 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____15614 ->
                        FStar_Pervasives_Native.Some uu____15614) uu____15611
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2139_15615 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2139_15615.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2139_15615.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let effect_args =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                  then
                    FStar_List.map
                      (fun uu____15678 ->
                         FStar_All.pipe_right FStar_Syntax_Syntax.unit_const
                           FStar_Syntax_Syntax.as_arg)
                  else
                    FStar_List.mapi
                      (fun idx ->
                         fun uu____15704 ->
                           match uu____15704 with
                           | (a, i) ->
                               let uu____15723 = norm cfg env1 [] a in
                               (uu____15723, i))) in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_15736 ->
                       match uu___14_15736 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15740 = norm cfg env1 [] t in
                           FStar_Syntax_Syntax.DECREASES uu____15740
                       | f -> f)) in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ in
             let uu___2157_15748 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2159_15751 = ct in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2159_15751.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2157_15748.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2157_15748.FStar_Syntax_Syntax.vars)
             })
and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg ->
    fun env1 ->
      fun b ->
        let uu____15755 = b in
        match uu____15755 with
        | (x, imp) ->
            let x1 =
              let uu___2167_15763 = x in
              let uu____15764 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2167_15763.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2167_15763.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15764
              } in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
                  let uu____15775 =
                    let uu____15776 =
                      let uu____15777 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____15777 in
                    FStar_Syntax_Syntax.Meta uu____15776 in
                  FStar_Pervasives_Native.Some uu____15775
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
                  let uu____15783 =
                    let uu____15784 =
                      let uu____15785 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____15785 in
                    FStar_Syntax_Syntax.Meta uu____15784 in
                  FStar_Pervasives_Native.Some uu____15783
              | i -> i in
            (x1, imp1)
and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu____15796 =
          FStar_List.fold_left
            (fun uu____15830 ->
               fun b ->
                 match uu____15830 with
                 | (nbs', env2) ->
                     let b1 = norm_binder cfg env2 b in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs in
        match uu____15796 with | (nbs, uu____15910) -> FStar_List.rev nbs
and (norm_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env1 ->
      fun lopt ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____15942 =
              let uu___2197_15943 = rc in
              let uu____15944 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2197_15943.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15944;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2197_15943.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15942
        | uu____15960 -> lopt
and (maybe_simplify :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let tm' = maybe_simplify_aux cfg env1 stack1 tm in
          if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.b380
          then
            (let uu____15969 = FStar_Syntax_Print.term_to_string tm in
             let uu____15970 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____15969 uu____15970)
          else ();
          tm'
and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg ->
    fun uu___15_15974 ->
      match uu___15_15974 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____15987 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l in
          (match uu____15987 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None ->
               let uu____15991 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None in
               FStar_Syntax_Syntax.fv_to_tm uu____15991)
and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let tm1 =
            let uu____15999 = norm_cb cfg in
            reduce_primops uu____15999 cfg env1 tm in
          let uu____16004 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify in
          if uu____16004
          then tm1
          else
            (let w t =
               let uu___2226_16018 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2226_16018.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2226_16018.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               let uu____16029 =
                 let uu____16030 = FStar_Syntax_Util.unmeta t in
                 uu____16030.FStar_Syntax_Syntax.n in
               match uu____16029 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16037 -> FStar_Pervasives_Native.None in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t, uu____16098)::args1, (bv, uu____16101)::bs1) ->
                   let uu____16155 =
                     let uu____16156 = FStar_Syntax_Subst.compress t in
                     uu____16156.FStar_Syntax_Syntax.n in
                   (match uu____16155 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16160 -> false)
               | ([], []) -> true
               | (uu____16189, uu____16190) -> false in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16239 = FStar_Syntax_Print.term_to_string t in
                  let uu____16240 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16239
                    uu____16240)
               else ();
               (let uu____16242 = FStar_Syntax_Util.head_and_args' t in
                match uu____16242 with
                | (hd, args) ->
                    let uu____16281 =
                      let uu____16282 = FStar_Syntax_Subst.compress hd in
                      uu____16282.FStar_Syntax_Syntax.n in
                    (match uu____16281 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____16289 =
                               FStar_Syntax_Print.term_to_string t in
                             let uu____16290 =
                               FStar_Syntax_Print.bv_to_string bv in
                             let uu____16291 =
                               FStar_Syntax_Print.term_to_string hd in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____16289 uu____16290 uu____16291)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____16293 -> FStar_Pervasives_Native.None)) in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16310 = FStar_Syntax_Print.term_to_string t in
                  let uu____16311 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____16310
                    uu____16311)
               else ();
               (let uu____16313 = FStar_Syntax_Util.is_squash t in
                match uu____16313 with
                | FStar_Pervasives_Native.Some (uu____16324, t') ->
                    is_applied bs t'
                | uu____16336 ->
                    let uu____16345 = FStar_Syntax_Util.is_auto_squash t in
                    (match uu____16345 with
                     | FStar_Pervasives_Native.Some (uu____16356, t') ->
                         is_applied bs t'
                     | uu____16368 -> is_applied bs t)) in
             let is_quantified_const bv phi =
               let uu____16392 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____16392 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid, (p, uu____16399)::(q, uu____16401)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16443 = FStar_Syntax_Print.term_to_string p in
                       let uu____16444 = FStar_Syntax_Print.term_to_string q in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____16443 uu____16444)
                    else ();
                    (let uu____16446 =
                       FStar_Syntax_Util.destruct_typ_as_formula p in
                     match uu____16446 with
                     | FStar_Pervasives_Native.None ->
                         let uu____16451 =
                           let uu____16452 = FStar_Syntax_Subst.compress p in
                           uu____16452.FStar_Syntax_Syntax.n in
                         (match uu____16451 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____16460 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q in
                                FStar_Pervasives_Native.Some uu____16460))
                          | uu____16463 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1, (p1, uu____16466)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____16491 =
                           let uu____16492 = FStar_Syntax_Subst.compress p1 in
                           uu____16492.FStar_Syntax_Syntax.n in
                         (match uu____16491 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____16500 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q in
                                FStar_Pervasives_Native.Some uu____16500))
                          | uu____16503 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs, pats, phi1)) ->
                         let uu____16507 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1 in
                         (match uu____16507 with
                          | FStar_Pervasives_Native.None ->
                              let uu____16512 =
                                is_applied_maybe_squashed bs phi1 in
                              (match uu____16512 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if
                                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 3\n"
                                    else ();
                                    (let ftrue =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_true
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0)) in
                                     let uu____16523 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____16523))
                               | uu____16526 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1, (p1, uu____16531)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____16556 =
                                is_applied_maybe_squashed bs p1 in
                              (match uu____16556 with
                               | FStar_Pervasives_Native.Some bv' when
                                   FStar_Syntax_Syntax.bv_eq bv bv' ->
                                   (if
                                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                                    then
                                      FStar_Util.print_string "WPE> Case 4\n"
                                    else ();
                                    (let ffalse =
                                       FStar_Syntax_Util.abs bs
                                         FStar_Syntax_Util.t_false
                                         (FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Util.residual_tot
                                               FStar_Syntax_Util.ktype0)) in
                                     let uu____16567 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____16567))
                               | uu____16570 -> FStar_Pervasives_Native.None)
                          | uu____16573 -> FStar_Pervasives_Native.None)
                     | uu____16576 -> FStar_Pervasives_Native.None))
               | uu____16579 -> FStar_Pervasives_Native.None in
             let is_forall_const phi =
               let uu____16592 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____16592 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv, uu____16598)::[], uu____16599, phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16618 = FStar_Syntax_Print.bv_to_string bv in
                       let uu____16619 =
                         FStar_Syntax_Print.term_to_string phi' in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____16618
                         uu____16619)
                    else ();
                    is_quantified_const bv phi')
               | uu____16621 -> FStar_Pervasives_Native.None in
             let is_const_match phi =
               let uu____16634 =
                 let uu____16635 = FStar_Syntax_Subst.compress phi in
                 uu____16635.FStar_Syntax_Syntax.n in
               match uu____16634 with
               | FStar_Syntax_Syntax.Tm_match (uu____16640, br::brs) ->
                   let uu____16707 = br in
                   (match uu____16707 with
                    | (uu____16724, uu____16725, e) ->
                        let r =
                          let uu____16746 = simp_t e in
                          match uu____16746 with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16752 =
                                FStar_List.for_all
                                  (fun uu____16770 ->
                                     match uu____16770 with
                                     | (uu____16783, uu____16784, e') ->
                                         let uu____16798 = simp_t e' in
                                         uu____16798 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs in
                              if uu____16752
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None in
                        r)
               | uu____16806 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____16815 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____16815
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16848 =
                 match uu____16848 with
                 | (t1, q) ->
                     let uu____16869 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____16869 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
                      | uu____16901 -> (t1, q)) in
               let uu____16914 = FStar_Syntax_Util.head_and_args t in
               match uu____16914 with
               | (head, args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     t.FStar_Syntax_Syntax.pos in
             let rec clearly_inhabited ty =
               let uu____16990 =
                 let uu____16991 = FStar_Syntax_Util.unmeta ty in
                 uu____16991.FStar_Syntax_Syntax.n in
               match uu____16990 with
               | FStar_Syntax_Syntax.Tm_uinst (t, uu____16995) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17000, c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17024 -> false in
             let simplify arg =
               let uu____17055 = simp_t (FStar_Pervasives_Native.fst arg) in
               (uu____17055, arg) in
             let uu____17068 = is_forall_const tm1 in
             match uu____17068 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____17073 = FStar_Syntax_Print.term_to_string tm1 in
                     let uu____17074 = FStar_Syntax_Print.term_to_string tm' in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____17073
                       uu____17074)
                  else ();
                  (let uu____17076 = norm cfg env1 [] tm' in
                   maybe_simplify_aux cfg env1 stack1 uu____17076))
             | FStar_Pervasives_Native.None ->
                 let uu____17077 =
                   let uu____17078 = FStar_Syntax_Subst.compress tm1 in
                   uu____17078.FStar_Syntax_Syntax.n in
                 (match uu____17077 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17082;
                              FStar_Syntax_Syntax.vars = uu____17083;_},
                            uu____17084);
                         FStar_Syntax_Syntax.pos = uu____17085;
                         FStar_Syntax_Syntax.vars = uu____17086;_},
                       args)
                      ->
                      let uu____17116 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____17116
                      then
                        let uu____17117 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____17117 with
                         | (FStar_Pervasives_Native.Some (true), uu____17172)::
                             (uu____17173, (arg, uu____17175))::[] ->
                             maybe_auto_squash arg
                         | (uu____17240, (arg, uu____17242))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____17243)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____17308)::uu____17309::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17372::(FStar_Pervasives_Native.Some
                                         (false), uu____17373)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17436 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17452 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____17452
                         then
                           let uu____17453 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____17453 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____17508)::uu____17509::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17572::(FStar_Pervasives_Native.Some
                                           (true), uu____17573)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____17636)::(uu____17637, (arg, uu____17639))::[]
                               -> maybe_auto_squash arg
                           | (uu____17704, (arg, uu____17706))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____17707)::[]
                               -> maybe_auto_squash arg
                           | uu____17772 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17788 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____17788
                            then
                              let uu____17789 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____17789 with
                              | uu____17844::(FStar_Pervasives_Native.Some
                                              (true), uu____17845)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____17908)::uu____17909::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____17972)::(uu____17973,
                                                (arg, uu____17975))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18040, (p, uu____18042))::(uu____18043,
                                                                  (q,
                                                                   uu____18045))::[]
                                  ->
                                  let uu____18110 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____18110
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18112 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18128 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____18128
                               then
                                 let uu____18129 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____18129 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18184)::(FStar_Pervasives_Native.Some
                                                   (true), uu____18185)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18250)::(FStar_Pervasives_Native.Some
                                                   (false), uu____18251)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18316)::(FStar_Pervasives_Native.Some
                                                   (false), uu____18317)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18382)::(FStar_Pervasives_Native.Some
                                                   (true), uu____18383)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18448, (arg, uu____18450))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____18451)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18516)::(uu____18517,
                                                   (arg, uu____18519))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18584, (arg, uu____18586))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____18587)::[]
                                     ->
                                     let uu____18652 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____18652
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18653)::(uu____18654,
                                                   (arg, uu____18656))::[]
                                     ->
                                     let uu____18721 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____18721
                                 | (uu____18722, (p, uu____18724))::(uu____18725,
                                                                    (q,
                                                                    uu____18727))::[]
                                     ->
                                     let uu____18792 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____18792
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18794 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18810 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____18810
                                  then
                                    let uu____18811 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____18811 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____18866)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____18905)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18944 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18960 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____18960
                                     then
                                       match args with
                                       | (t, uu____18962)::[] ->
                                           let uu____18987 =
                                             let uu____18988 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____18988.FStar_Syntax_Syntax.n in
                                           (match uu____18987 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18991::[], body,
                                                 uu____18993)
                                                ->
                                                let uu____19028 = simp_t body in
                                                (match uu____19028 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19031 -> tm1)
                                            | uu____19034 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19036))::(t, uu____19038)::[]
                                           ->
                                           let uu____19077 =
                                             let uu____19078 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____19078.FStar_Syntax_Syntax.n in
                                           (match uu____19077 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19081::[], body,
                                                 uu____19083)
                                                ->
                                                let uu____19118 = simp_t body in
                                                (match uu____19118 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19121 -> tm1)
                                            | uu____19124 -> tm1)
                                       | uu____19125 -> tm1
                                     else
                                       (let uu____19137 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____19137
                                        then
                                          match args with
                                          | (t, uu____19139)::[] ->
                                              let uu____19164 =
                                                let uu____19165 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____19165.FStar_Syntax_Syntax.n in
                                              (match uu____19164 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19168::[], body,
                                                    uu____19170)
                                                   ->
                                                   let uu____19205 =
                                                     simp_t body in
                                                   (match uu____19205 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19208 -> tm1)
                                               | uu____19211 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19213))::(t, uu____19215)::[]
                                              ->
                                              let uu____19254 =
                                                let uu____19255 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____19255.FStar_Syntax_Syntax.n in
                                              (match uu____19254 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19258::[], body,
                                                    uu____19260)
                                                   ->
                                                   let uu____19295 =
                                                     simp_t body in
                                                   (match uu____19295 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____19298 -> tm1)
                                               | uu____19301 -> tm1)
                                          | uu____19302 -> tm1
                                        else
                                          (let uu____19314 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____19314
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19315;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19316;_},
                                                uu____19317)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19342;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19343;_},
                                                uu____19344)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19369 -> tm1
                                           else
                                             (let uu____19381 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____19381
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____19391 =
                                                    let uu____19392 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____19392.FStar_Syntax_Syntax.n in
                                                  match uu____19391 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____19400 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____19410 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____19410
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____19445 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____19445
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____19447 =
                                                         let uu____19448 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____19448.FStar_Syntax_Syntax.n in
                                                       match uu____19447 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____19451 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____19459 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____19459
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____19464
                                                                  =
                                                                  let uu____19465
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____19465.FStar_Syntax_Syntax.n in
                                                                match uu____19464
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____19471)
                                                                    -> hd
                                                                | uu____19496
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____19499
                                                                =
                                                                let uu____19510
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____19510] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____19499)
                                                       | uu____19543 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____19546 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____19546 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____19566 ->
                                                     let uu____19575 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____19575 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____19581;
                         FStar_Syntax_Syntax.vars = uu____19582;_},
                       args)
                      ->
                      let uu____19608 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____19608
                      then
                        let uu____19609 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____19609 with
                         | (FStar_Pervasives_Native.Some (true), uu____19664)::
                             (uu____19665, (arg, uu____19667))::[] ->
                             maybe_auto_squash arg
                         | (uu____19732, (arg, uu____19734))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____19735)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____19800)::uu____19801::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19864::(FStar_Pervasives_Native.Some
                                         (false), uu____19865)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19928 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19944 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____19944
                         then
                           let uu____19945 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____19945 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____20000)::uu____20001::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20064::(FStar_Pervasives_Native.Some
                                           (true), uu____20065)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____20128)::(uu____20129, (arg, uu____20131))::[]
                               -> maybe_auto_squash arg
                           | (uu____20196, (arg, uu____20198))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____20199)::[]
                               -> maybe_auto_squash arg
                           | uu____20264 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20280 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____20280
                            then
                              let uu____20281 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____20281 with
                              | uu____20336::(FStar_Pervasives_Native.Some
                                              (true), uu____20337)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____20400)::uu____20401::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____20464)::(uu____20465,
                                                (arg, uu____20467))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20532, (p, uu____20534))::(uu____20535,
                                                                  (q,
                                                                   uu____20537))::[]
                                  ->
                                  let uu____20602 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____20602
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20604 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20620 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____20620
                               then
                                 let uu____20621 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____20621 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20676)::(FStar_Pervasives_Native.Some
                                                   (true), uu____20677)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20742)::(FStar_Pervasives_Native.Some
                                                   (false), uu____20743)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20808)::(FStar_Pervasives_Native.Some
                                                   (false), uu____20809)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20874)::(FStar_Pervasives_Native.Some
                                                   (true), uu____20875)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20940, (arg, uu____20942))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____20943)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____21008)::(uu____21009,
                                                   (arg, uu____21011))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21076, (arg, uu____21078))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____21079)::[]
                                     ->
                                     let uu____21144 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____21144
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____21145)::(uu____21146,
                                                   (arg, uu____21148))::[]
                                     ->
                                     let uu____21213 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____21213
                                 | (uu____21214, (p, uu____21216))::(uu____21217,
                                                                    (q,
                                                                    uu____21219))::[]
                                     ->
                                     let uu____21284 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____21284
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21286 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21302 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____21302
                                  then
                                    let uu____21303 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____21303 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____21358)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____21397)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21436 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21452 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____21452
                                     then
                                       match args with
                                       | (t, uu____21454)::[] ->
                                           let uu____21479 =
                                             let uu____21480 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____21480.FStar_Syntax_Syntax.n in
                                           (match uu____21479 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21483::[], body,
                                                 uu____21485)
                                                ->
                                                let uu____21520 = simp_t body in
                                                (match uu____21520 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21523 -> tm1)
                                            | uu____21526 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21528))::(t, uu____21530)::[]
                                           ->
                                           let uu____21569 =
                                             let uu____21570 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____21570.FStar_Syntax_Syntax.n in
                                           (match uu____21569 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21573::[], body,
                                                 uu____21575)
                                                ->
                                                let uu____21610 = simp_t body in
                                                (match uu____21610 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21613 -> tm1)
                                            | uu____21616 -> tm1)
                                       | uu____21617 -> tm1
                                     else
                                       (let uu____21629 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____21629
                                        then
                                          match args with
                                          | (t, uu____21631)::[] ->
                                              let uu____21656 =
                                                let uu____21657 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____21657.FStar_Syntax_Syntax.n in
                                              (match uu____21656 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21660::[], body,
                                                    uu____21662)
                                                   ->
                                                   let uu____21697 =
                                                     simp_t body in
                                                   (match uu____21697 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21700 -> tm1)
                                               | uu____21703 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21705))::(t, uu____21707)::[]
                                              ->
                                              let uu____21746 =
                                                let uu____21747 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____21747.FStar_Syntax_Syntax.n in
                                              (match uu____21746 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21750::[], body,
                                                    uu____21752)
                                                   ->
                                                   let uu____21787 =
                                                     simp_t body in
                                                   (match uu____21787 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____21790 -> tm1)
                                               | uu____21793 -> tm1)
                                          | uu____21794 -> tm1
                                        else
                                          (let uu____21806 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____21806
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21807;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21808;_},
                                                uu____21809)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21834;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21835;_},
                                                uu____21836)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21861 -> tm1
                                           else
                                             (let uu____21873 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____21873
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____21883 =
                                                    let uu____21884 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____21884.FStar_Syntax_Syntax.n in
                                                  match uu____21883 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21892 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21902 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____21902
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____21941 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____21941
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21943 =
                                                         let uu____21944 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____21944.FStar_Syntax_Syntax.n in
                                                       match uu____21943 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21947 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____21955 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____21955
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21960
                                                                  =
                                                                  let uu____21961
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____21961.FStar_Syntax_Syntax.n in
                                                                match uu____21960
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____21967)
                                                                    -> hd
                                                                | uu____21992
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____21995
                                                                =
                                                                let uu____22006
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____22006] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21995)
                                                       | uu____22039 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22042 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____22042 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22062 ->
                                                     let uu____22071 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____22071 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
                      let uu____22082 = simp_t t in
                      (match uu____22082 with
                       | FStar_Pervasives_Native.Some (true) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false) -> tm1
                       | FStar_Pervasives_Native.None -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22085 ->
                      let uu____22108 = is_const_match tm1 in
                      (match uu____22108 with
                       | FStar_Pervasives_Native.Some (true) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None -> tm1)
                  | uu____22111 -> tm1))
and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____22121 ->
               (let uu____22123 = FStar_Syntax_Print.tag_of_term t in
                let uu____22124 = FStar_Syntax_Print.term_to_string t in
                let uu____22125 =
                  FStar_Util.string_of_int (FStar_List.length env1) in
                let uu____22132 =
                  let uu____22133 =
                    let uu____22136 = firstn (Prims.of_int (4)) stack1 in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22136 in
                  stack_to_string uu____22133 in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22123 uu____22124 uu____22125 uu____22132);
               (let uu____22159 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild") in
                if uu____22159
                then
                  let uu____22160 = FStar_Syntax_Util.unbound_variables t in
                  match uu____22160 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22167 = FStar_Syntax_Print.tag_of_term t in
                        let uu____22168 = FStar_Syntax_Print.term_to_string t in
                        let uu____22169 =
                          let uu____22170 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string) in
                          FStar_All.pipe_right uu____22170
                            (FStar_String.concat ", ") in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22167
                          uu____22168 uu____22169);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t in
           let uu____22183 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____22188)::uu____22189 -> true
                | uu____22198 -> false) in
           if uu____22183
           then
             let uu____22199 = FStar_All.pipe_right f_opt FStar_Util.must in
             FStar_All.pipe_right uu____22199 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t in
              match stack1 with
              | [] -> t1
              | (Debug (tm, time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now () in
                      let uu____22211 =
                        let uu____22212 =
                          let uu____22213 =
                            FStar_Util.time_diff time_then time_now in
                          FStar_Pervasives_Native.snd uu____22213 in
                        FStar_Util.string_of_int uu____22212 in
                      let uu____22218 = FStar_Syntax_Print.term_to_string tm in
                      let uu____22219 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg in
                      let uu____22220 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____22211 uu____22218 uu____22219 uu____22220)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____22226, m, r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____22255 ->
                        let uu____22256 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1 "\tSet memo %s\n" uu____22256);
                   rebuild cfg env1 stack2 t1)
              | (Let (env', bs, lb, r))::stack2 ->
                  let body = FStar_Syntax_Subst.close bs t1 in
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) r in
                  rebuild cfg env' stack2 t2
              | (Abs (env', bs, env'', lopt, r))::stack2 ->
                  let bs1 = norm_binders cfg env' bs in
                  let lopt1 = norm_lcomp_opt cfg env'' lopt in
                  let uu____22294 =
                    let uu___2855_22295 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2855_22295.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2855_22295.FStar_Syntax_Syntax.vars)
                    } in
                  rebuild cfg env1 stack2 uu____22294
              | (Arg
                  (Univ uu____22298, uu____22299, uu____22300))::uu____22301
                  -> failwith "Impossible"
              | (Arg (Dummy, uu____22304, uu____22305))::uu____22306 ->
                  failwith "Impossible"
              | (UnivArgs (us, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg, tm, uu____22321, uu____22322), aq, r))::stack2
                  when
                  let uu____22372 = head_of t1 in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22372 ->
                  let t2 =
                    let uu____22374 =
                      let uu____22375 = closure_as_term cfg env_arg tm in
                      (uu____22375, aq) in
                    FStar_Syntax_Syntax.extend_app t1 uu____22374 r in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg, tm, m, uu____22385), aq, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____22438 ->
                        let uu____22439 =
                          FStar_Syntax_Print.term_to_string tm in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____22439);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (let uu____22440 =
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          &&
                          (let uu____22442 = is_partial_primop_app cfg t1 in
                           Prims.op_Negation uu____22442) in
                      if uu____22440
                      then
                        let arg = closure_as_term cfg env_arg tm in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2 in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu____22454 = FStar_ST.op_Bang m in
                      match uu____22454 with
                      | FStar_Pervasives_Native.None ->
                          let uu____22515 =
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                              &&
                              (let uu____22517 = is_partial_primop_app cfg t1 in
                               Prims.op_Negation uu____22517) in
                          if uu____22515
                          then
                            let arg = closure_as_term cfg env_arg tm in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                            rebuild cfg env_arg stack2 t2
                          else
                            (let stack3 = (MemoLazy m) ::
                               (App (env1, t1, aq, r)) :: stack2 in
                             norm cfg env_arg stack3 tm)
                      | FStar_Pervasives_Native.Some (uu____22528, a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq) r in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2, head, aq, r))::stack' when
                  should_reify cfg stack1 ->
                  let t0 = t1 in
                  let fallback msg uu____22581 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____22585 ->
                         let uu____22586 =
                           FStar_Syntax_Print.term_to_string t1 in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____22586);
                    (let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                     rebuild cfg env2 stack' t2) in
                  let is_layered_effect m =
                    let uu____22598 =
                      FStar_All.pipe_right m
                        (FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv) in
                    FStar_All.pipe_right uu____22598
                      (FStar_TypeChecker_Env.is_layered_effect
                         cfg.FStar_TypeChecker_Cfg.tcenv) in
                  let uu____22599 =
                    let uu____22600 = FStar_Syntax_Subst.compress t1 in
                    uu____22600.FStar_Syntax_Syntax.n in
                  (match uu____22599 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____22603, FStar_Syntax_Syntax.Meta_monadic
                        (m, uu____22605))
                       when
                       (FStar_All.pipe_right m is_layered_effect) &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu____22614 =
                         let uu____22615 = FStar_Ident.string_of_lid m in
                         FStar_Util.format1
                           "Meta_monadic for a layered effect %s in non-extraction mode"
                           uu____22615 in
                       fallback uu____22614 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____22616, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, uu____22619))
                       when
                       ((is_layered_effect msrc) || (is_layered_effect mtgt))
                         &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu____22628 =
                         let uu____22629 = FStar_Ident.string_of_lid msrc in
                         let uu____22630 = FStar_Ident.string_of_lid mtgt in
                         FStar_Util.format2
                           "Meta_monadic_lift for layered effect %s ~> %s in non extraction mode"
                           uu____22629 uu____22630 in
                       fallback uu____22628 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, ty))
                       ->
                       let lifted =
                         let uu____22655 = closure_as_term cfg env2 ty in
                         reify_lift cfg t2 msrc mtgt uu____22655 in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____22659 ->
                             let uu____22660 =
                               FStar_Syntax_Print.term_to_string lifted in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____22660);
                        (let uu____22661 = FStar_List.tl stack1 in
                         norm cfg env2 uu____22661 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____22662);
                          FStar_Syntax_Syntax.pos = uu____22663;
                          FStar_Syntax_Syntax.vars = uu____22664;_},
                        (e, uu____22666)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____22705 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____22722 = FStar_Syntax_Util.head_and_args t1 in
                       (match uu____22722 with
                        | (hd, args) ->
                            let uu____22765 =
                              let uu____22766 = FStar_Syntax_Util.un_uinst hd in
                              uu____22766.FStar_Syntax_Syntax.n in
                            (match uu____22765 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____22770 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv in
                                 (match uu____22770 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____22773;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____22774;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____22775;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____22777;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____22778;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____22779;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____22780;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____22809 -> fallback " (3)" ())
                             | uu____22812 -> fallback " (4)" ()))
                   | uu____22813 -> fallback " (2)" ())
              | (App (env2, head, aq, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env', head, aq, r))::stack2 ->
                  let uu____22833 =
                    let uu____22834 =
                      let uu____22835 =
                        let uu____22842 =
                          let uu____22843 =
                            let uu____22874 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            (env1, t1, uu____22874, false) in
                          Clos uu____22843 in
                        (uu____22842, aq, (t1.FStar_Syntax_Syntax.pos)) in
                      Arg uu____22835 in
                    uu____22834 :: stack2 in
                  norm cfg env' uu____22833 head
              | (Match (env', branches1, cfg1, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____22947 ->
                        let uu____22948 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____22948);
                   (let scrutinee_env = env1 in
                    let env2 = env' in
                    let scrutinee = t1 in
                    let norm_and_rebuild_match uu____22957 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____22962 ->
                           let uu____22963 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           let uu____22964 =
                             let uu____22965 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____22992 ->
                                       match uu____22992 with
                                       | (p, uu____23002, uu____23003) ->
                                           FStar_Syntax_Print.pat_to_string p)) in
                             FStar_All.pipe_right uu____22965
                               (FStar_String.concat "\n\t") in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____22963 uu____22964);
                      (let whnf =
                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                           ||
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf in
                       let cfg_exclude_zeta =
                         if
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full
                         then cfg1
                         else
                           (let new_delta =
                              FStar_All.pipe_right
                                cfg1.FStar_TypeChecker_Cfg.delta_level
                                (FStar_List.filter
                                   (fun uu___16_23021 ->
                                      match uu___16_23021 with
                                      | FStar_TypeChecker_Env.InliningDelta
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                          -> true
                                      | uu____23022 -> false)) in
                            let steps =
                              let uu___3049_23024 =
                                cfg1.FStar_TypeChecker_Cfg.steps in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3049_23024.FStar_TypeChecker_Cfg.for_extraction)
                              } in
                            let uu___3052_23029 = cfg1 in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3052_23029.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3052_23029.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3052_23029.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3052_23029.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3052_23029.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3052_23029.FStar_TypeChecker_Cfg.reifying)
                            }) in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2 in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____23101 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                             let uu____23130 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____23214 ->
                                       fun uu____23215 ->
                                         match (uu____23214, uu____23215)
                                         with
                                         | ((pats1, env4), (p1, b)) ->
                                             let uu____23354 =
                                               norm_pat env4 p1 in
                                             (match uu____23354 with
                                              | (p2, env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3)) in
                             (match uu____23130 with
                              | (pats1, env4) ->
                                  ((let uu___3080_23516 = p in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3080_23516.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3084_23535 = x in
                               let uu____23536 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3084_23535.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3084_23535.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____23536
                               } in
                             ((let uu___3087_23550 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3087_23550.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3091_23561 = x in
                               let uu____23562 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3091_23561.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3091_23561.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____23562
                               } in
                             ((let uu___3094_23576 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3094_23576.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                             let x1 =
                               let uu___3100_23592 = x in
                               let uu____23593 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3100_23592.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3100_23592.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____23593
                               } in
                             let t3 = norm_or_whnf env3 t2 in
                             ((let uu___3104_23608 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3104_23608.FStar_Syntax_Syntax.p)
                               }), env3) in
                       let norm_branches uu____23628 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____23645 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch ->
                                     let uu____23661 =
                                       FStar_Syntax_Subst.open_branch branch in
                                     match uu____23661 with
                                     | (p, wopt, e) ->
                                         let uu____23681 = norm_pat env2 p in
                                         (match uu____23681 with
                                          | (p1, env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____23736 =
                                                      norm_or_whnf env3 w in
                                                    FStar_Pervasives_Native.Some
                                                      uu____23736 in
                                              let e1 = norm_or_whnf env3 e in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1)))) in
                       let maybe_commute_matches uu____23755 =
                         let can_commute =
                           match branches1 with
                           | ({
                                FStar_Syntax_Syntax.v =
                                  FStar_Syntax_Syntax.Pat_cons
                                  (fv, uu____23758);
                                FStar_Syntax_Syntax.p = uu____23759;_},
                              uu____23760, uu____23761)::uu____23762 ->
                               FStar_TypeChecker_Env.fv_has_attr
                                 cfg1.FStar_TypeChecker_Cfg.tcenv fv
                                 FStar_Parser_Const.commute_nested_matches_lid
                           | uu____23801 -> false in
                         let uu____23802 =
                           let uu____23803 =
                             FStar_Syntax_Util.unascribe scrutinee in
                           uu____23803.FStar_Syntax_Syntax.n in
                         match uu____23802 with
                         | FStar_Syntax_Syntax.Tm_match (sc0, branches0) when
                             can_commute ->
                             let reduce_branch b =
                               let stack3 =
                                 [Match (env', branches1, cfg1, r)] in
                               let uu____23853 =
                                 FStar_Syntax_Subst.open_branch b in
                               match uu____23853 with
                               | (p, wopt, e) ->
                                   let uu____23873 = norm_pat scrutinee_env p in
                                   (match uu____23873 with
                                    | (p1, branch_env) ->
                                        let wopt1 =
                                          match wopt with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____23928 =
                                                norm_or_whnf branch_env w in
                                              FStar_Pervasives_Native.Some
                                                uu____23928 in
                                        let e1 =
                                          norm cfg1 branch_env stack3 e in
                                        FStar_Syntax_Util.branch
                                          (p1, wopt1, e1)) in
                             let branches01 =
                               FStar_List.map reduce_branch branches0 in
                             let uu____23987 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (sc0, branches01)) r in
                             rebuild cfg1 env2 stack2 uu____23987
                         | uu____24006 ->
                             let scrutinee1 =
                               let uu____24010 =
                                 ((((cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                                      &&
                                      (Prims.op_Negation
                                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak))
                                     &&
                                     (Prims.op_Negation
                                        (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars))
                                    &&
                                    (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                                   && (maybe_weakly_reduced scrutinee) in
                               if uu____24010
                               then
                                 norm
                                   (let uu___3160_24015 = cfg1 in
                                    {
                                      FStar_TypeChecker_Cfg.steps =
                                        (let uu___3162_24018 =
                                           cfg1.FStar_TypeChecker_Cfg.steps in
                                         {
                                           FStar_TypeChecker_Cfg.beta =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.beta);
                                           FStar_TypeChecker_Cfg.iota =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.iota);
                                           FStar_TypeChecker_Cfg.zeta =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.zeta);
                                           FStar_TypeChecker_Cfg.zeta_full =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.zeta_full);
                                           FStar_TypeChecker_Cfg.weak =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.weak);
                                           FStar_TypeChecker_Cfg.hnf =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.hnf);
                                           FStar_TypeChecker_Cfg.primops =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.primops);
                                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                           FStar_TypeChecker_Cfg.unfold_until
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.unfold_until);
                                           FStar_TypeChecker_Cfg.unfold_only
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.unfold_only);
                                           FStar_TypeChecker_Cfg.unfold_fully
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.unfold_fully);
                                           FStar_TypeChecker_Cfg.unfold_attr
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.unfold_attr);
                                           FStar_TypeChecker_Cfg.unfold_tac =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.unfold_tac);
                                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                           FStar_TypeChecker_Cfg.simplify =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.simplify);
                                           FStar_TypeChecker_Cfg.erase_universes
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.erase_universes);
                                           FStar_TypeChecker_Cfg.allow_unbound_universes
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                           FStar_TypeChecker_Cfg.reify_ =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.reify_);
                                           FStar_TypeChecker_Cfg.compress_uvars
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.compress_uvars);
                                           FStar_TypeChecker_Cfg.no_full_norm
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.no_full_norm);
                                           FStar_TypeChecker_Cfg.check_no_uvars
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.check_no_uvars);
                                           FStar_TypeChecker_Cfg.unmeta =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.unmeta);
                                           FStar_TypeChecker_Cfg.unascribe =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.unascribe);
                                           FStar_TypeChecker_Cfg.in_full_norm_request
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.in_full_norm_request);
                                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                             = false;
                                           FStar_TypeChecker_Cfg.nbe_step =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.nbe_step);
                                           FStar_TypeChecker_Cfg.for_extraction
                                             =
                                             (uu___3162_24018.FStar_TypeChecker_Cfg.for_extraction)
                                         });
                                      FStar_TypeChecker_Cfg.tcenv =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.tcenv);
                                      FStar_TypeChecker_Cfg.debug =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.debug);
                                      FStar_TypeChecker_Cfg.delta_level =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.delta_level);
                                      FStar_TypeChecker_Cfg.primitive_steps =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.primitive_steps);
                                      FStar_TypeChecker_Cfg.strong =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.strong);
                                      FStar_TypeChecker_Cfg.memoize_lazy =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.memoize_lazy);
                                      FStar_TypeChecker_Cfg.normalize_pure_lets
                                        =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                      FStar_TypeChecker_Cfg.reifying =
                                        (uu___3160_24015.FStar_TypeChecker_Cfg.reifying)
                                    }) scrutinee_env [] scrutinee
                               else scrutinee in
                             let branches2 = norm_branches () in
                             let uu____24031 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (scrutinee1, branches2)) r in
                             rebuild cfg1 env2 stack2 uu____24031 in
                       maybe_commute_matches ()) in
                    let rec is_cons head =
                      let uu____24056 =
                        let uu____24057 = FStar_Syntax_Subst.compress head in
                        uu____24057.FStar_Syntax_Syntax.n in
                      match uu____24056 with
                      | FStar_Syntax_Syntax.Tm_uinst (h, uu____24061) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____24066 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24067;
                            FStar_Syntax_Syntax.fv_delta = uu____24068;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor);_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24069;
                            FStar_Syntax_Syntax.fv_delta = uu____24070;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____24071);_}
                          -> true
                      | uu____24078 -> false in
                    let guard_when_clause wopt b rest =
                      match wopt with
                      | FStar_Pervasives_Native.None -> b
                      | FStar_Pervasives_Native.Some w ->
                          let then_branch = b in
                          let else_branch =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                              r in
                          FStar_Syntax_Util.if_then_else w then_branch
                            else_branch in
                    let rec matches_pat scrutinee_orig p =
                      let scrutinee1 =
                        FStar_Syntax_Util.unmeta scrutinee_orig in
                      let scrutinee2 = FStar_Syntax_Util.unlazy scrutinee1 in
                      let uu____24242 =
                        FStar_Syntax_Util.head_and_args scrutinee2 in
                      match uu____24242 with
                      | (head, args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____24335 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____24374 ->
                                    let uu____24375 =
                                      let uu____24376 = is_cons head in
                                      Prims.op_Negation uu____24376 in
                                    FStar_Util.Inr uu____24375)
                           | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                               let uu____24401 =
                                 let uu____24402 =
                                   FStar_Syntax_Util.un_uinst head in
                                 uu____24402.FStar_Syntax_Syntax.n in
                               (match uu____24401 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____24420 ->
                                    let uu____24421 =
                                      let uu____24422 = is_cons head in
                                      Prims.op_Negation uu____24422 in
                                    FStar_Util.Inr uu____24421))
                    and matches_args out a p =
                      match (a, p) with
                      | ([], []) -> FStar_Util.Inl out
                      | ((t2, uu____24505)::rest_a,
                         (p1, uu____24508)::rest_p) ->
                          let uu____24562 = matches_pat t2 p1 in
                          (match uu____24562 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____24611 -> FStar_Util.Inr false in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1, wopt, b)::rest ->
                          let uu____24731 = matches_pat scrutinee1 p1 in
                          (match uu____24731 with
                           | FStar_Util.Inr (false) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____24771 ->
                                     let uu____24772 =
                                       FStar_Syntax_Print.pat_to_string p1 in
                                     let uu____24773 =
                                       let uu____24774 =
                                         FStar_List.map
                                           (fun uu____24784 ->
                                              match uu____24784 with
                                              | (uu____24789, t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s in
                                       FStar_All.pipe_right uu____24774
                                         (FStar_String.concat "; ") in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____24772 uu____24773);
                                (let env0 = env2 in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3 ->
                                        fun uu____24821 ->
                                          match uu____24821 with
                                          | (bv, t2) ->
                                              let uu____24844 =
                                                let uu____24851 =
                                                  let uu____24854 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv in
                                                  FStar_Pervasives_Native.Some
                                                    uu____24854 in
                                                let uu____24855 =
                                                  let uu____24856 =
                                                    let uu____24887 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2)) in
                                                    ([], t2, uu____24887,
                                                      false) in
                                                  Clos uu____24856 in
                                                (uu____24851, uu____24855) in
                                              uu____24844 :: env3) env2 s in
                                 let uu____24978 =
                                   guard_when_clause wopt b rest in
                                 norm cfg1 env3 stack2 uu____24978))) in
                    if
                      (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    then matches scrutinee branches1
                    else norm_and_rebuild_match ()))))
let (reflection_env_hook :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (normalize_with_primitive_steps :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps ->
    fun s ->
      fun e ->
        fun t ->
          let c = FStar_TypeChecker_Cfg.config' ps s e in
          FStar_ST.op_Colon_Equals reflection_env_hook
            (FStar_Pervasives_Native.Some e);
          FStar_TypeChecker_Cfg.log_cfg c
            (fun uu____25025 ->
               let uu____25026 = FStar_TypeChecker_Cfg.cfg_to_string c in
               FStar_Util.print1 "Cfg = %s\n" uu____25026);
          (let uu____25027 = is_nbe_request s in
           if uu____25027
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25031 ->
                   let uu____25032 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____25032);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25036 ->
                   let uu____25037 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25037);
              (let uu____25038 =
                 FStar_Util.record_time (fun uu____25044 -> nbe_eval c s t) in
               match uu____25038 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25051 ->
                         let uu____25052 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____25053 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25052 uu____25053);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25058 ->
                   let uu____25059 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____25059);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25063 ->
                   let uu____25064 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25064);
              (let uu____25065 =
                 FStar_Util.record_time (fun uu____25071 -> norm c [] [] t) in
               match uu____25065 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25084 ->
                         let uu____25085 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____25086 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25085 uu____25086);
                    r))))
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        let uu____25102 =
          let uu____25105 =
            let uu____25106 = FStar_TypeChecker_Env.current_module e in
            FStar_Ident.string_of_lid uu____25106 in
          FStar_Pervasives_Native.Some uu____25105 in
        FStar_Profiling.profile
          (fun uu____25108 -> normalize_with_primitive_steps [] s e t)
          uu____25102 "FStar.TypeChecker.Normalize"
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s ->
    fun e ->
      fun c ->
        let cfg = FStar_TypeChecker_Cfg.config s e in
        FStar_ST.op_Colon_Equals reflection_env_hook
          (FStar_Pervasives_Native.Some e);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____25139 ->
             let uu____25140 = FStar_Syntax_Print.comp_to_string c in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____25140);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____25144 ->
             let uu____25145 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
             FStar_Util.print1 ">>> cfg = %s\n" uu____25145);
        (let uu____25146 =
           FStar_Util.record_time (fun uu____25152 -> norm_comp cfg [] c) in
         match uu____25146 with
         | (c1, ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____25165 ->
                   let uu____25166 = FStar_Syntax_Print.comp_to_string c1 in
                   let uu____25167 = FStar_Util.string_of_int ms in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____25166
                     uu____25167);
              c1))
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1 ->
    fun u ->
      let uu____25178 = FStar_TypeChecker_Cfg.config [] env1 in
      norm_universe uu____25178 [] u
let (non_info_norm :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.HNF;
        FStar_TypeChecker_Env.Unascribe;
        FStar_TypeChecker_Env.ForExtraction] in
      let uu____25198 = normalize steps env1 t in
      FStar_TypeChecker_Env.non_informative env1 uu____25198
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1 ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25209 -> c
      | FStar_Syntax_Syntax.GTotal (t, uopt) when non_info_norm env1 t ->
          let uu___3333_25228 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3333_25228.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3333_25228.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____25235 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ) in
          if uu____25235
          then
            let ct1 =
              let uu____25237 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name in
              match uu____25237 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____25244 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu____25244
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___3343_25248 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3343_25248.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3343_25248.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3343_25248.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c in
                  let uu___3347_25250 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3347_25250.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3347_25250.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3347_25250.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3347_25250.FStar_Syntax_Syntax.flags)
                  } in
            let uu___3350_25251 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3350_25251.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3350_25251.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25253 -> c
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1 ->
    fun lc ->
      let uu____25264 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ) in
      if uu____25264
      then
        let uu____25265 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name in
        match uu____25265 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3358_25269 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g -> g) lc in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3358_25269.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3358_25269.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3358_25269.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None -> lc
      else lc
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1 ->
    fun t ->
      let t1 =
        try
          (fun uu___3365_25285 ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3364_25288 ->
            ((let uu____25290 =
                let uu____25295 =
                  let uu____25296 = FStar_Util.message_of_exn uu___3364_25288 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25296 in
                (FStar_Errors.Warning_NormalizationFailure, uu____25295) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25290);
             t) in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1 ->
    fun c ->
      let c1 =
        try
          (fun uu___3375_25310 ->
             match () with
             | () ->
                 let uu____25311 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1 in
                 norm_comp uu____25311 [] c) ()
        with
        | uu___3374_25320 ->
            ((let uu____25322 =
                let uu____25327 =
                  let uu____25328 = FStar_Util.message_of_exn uu___3374_25320 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25328 in
                (FStar_Errors.Warning_NormalizationFailure, uu____25327) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25322);
             c) in
      FStar_Syntax_Print.comp_to_string' env1.FStar_TypeChecker_Env.dsenv c1
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps ->
    fun env1 ->
      fun t0 ->
        let t =
          normalize (FStar_List.append steps [FStar_TypeChecker_Env.Beta])
            env1 t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y, phi1) ->
                   let uu____25373 =
                     let uu____25374 =
                       let uu____25381 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi in
                       (y, uu____25381) in
                     FStar_Syntax_Syntax.Tm_refine uu____25374 in
                   FStar_Syntax_Syntax.mk uu____25373
                     t01.FStar_Syntax_Syntax.pos
               | uu____25386 -> t2)
          | uu____25387 -> t2 in
        aux t
let (whnf_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Weak;
  FStar_TypeChecker_Env.HNF;
  FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
  FStar_TypeChecker_Env.Beta]
let (unfold_whnf' :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env1 ->
      fun t -> normalize (FStar_List.append steps whnf_steps) env1 t
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1 -> fun t -> unfold_whnf' [] env1 t
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove ->
    fun env1 ->
      fun t ->
        normalize
          (FStar_List.append
             (if remove then [FStar_TypeChecker_Env.CheckNoUvars] else [])
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.DoNotUnfoldPureLets;
             FStar_TypeChecker_Env.CompressUvars;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Iota;
             FStar_TypeChecker_Env.NoFullNorm]) env1 t
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1 -> fun t -> reduce_or_remove_uvar_solutions false env1 t
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1 -> fun t -> reduce_or_remove_uvar_solutions true env1 t
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun e ->
      fun t_e ->
        let uu____25468 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____25468 with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu____25481 ->
                 let uu____25482 = FStar_Syntax_Util.abs_formals e in
                 (match uu____25482 with
                  | (actuals, uu____25492, uu____25493) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25511 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____25511 with
                         | (binders, args) ->
                             let uu____25522 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____25522
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env1 t x.FStar_Syntax_Syntax.sort
      | uu____25536 ->
          let uu____25537 = FStar_Syntax_Util.head_and_args t in
          (match uu____25537 with
           | (head, args) ->
               let uu____25580 =
                 let uu____25581 = FStar_Syntax_Subst.compress head in
                 uu____25581.FStar_Syntax_Syntax.n in
               (match uu____25580 with
                | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
                    let uu____25602 =
                      let uu____25609 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ in
                      FStar_Syntax_Util.arrow_formals uu____25609 in
                    (match uu____25602 with
                     | (formals, _tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25631 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3445_25639 = env1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3445_25639.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3445_25639.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3445_25639.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3445_25639.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3445_25639.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3445_25639.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3445_25639.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3445_25639.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3445_25639.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3445_25639.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3445_25639.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3445_25639.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3445_25639.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3445_25639.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3445_25639.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3445_25639.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3445_25639.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3445_25639.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3445_25639.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3445_25639.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3445_25639.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3445_25639.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3445_25639.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3445_25639.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3445_25639.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3445_25639.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3445_25639.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3445_25639.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3445_25639.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3445_25639.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3445_25639.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3445_25639.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3445_25639.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3445_25639.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3445_25639.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3445_25639.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3445_25639.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3445_25639.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3445_25639.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3445_25639.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3445_25639.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3445_25639.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3445_25639.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___3445_25639.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) t in
                            match uu____25631 with
                            | (uu____25640, ty, uu____25642) ->
                                eta_expand_with_type env1 t ty))
                | uu____25643 ->
                    let uu____25644 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3452_25652 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3452_25652.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3452_25652.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3452_25652.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3452_25652.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3452_25652.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3452_25652.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3452_25652.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3452_25652.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3452_25652.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3452_25652.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3452_25652.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3452_25652.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3452_25652.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3452_25652.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3452_25652.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3452_25652.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3452_25652.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3452_25652.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3452_25652.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3452_25652.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3452_25652.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3452_25652.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3452_25652.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3452_25652.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3452_25652.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3452_25652.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3452_25652.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3452_25652.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3452_25652.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3452_25652.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3452_25652.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3452_25652.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3452_25652.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3452_25652.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3452_25652.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3452_25652.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3452_25652.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3452_25652.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3452_25652.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3452_25652.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3452_25652.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3452_25652.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3452_25652.FStar_TypeChecker_Env.erasable_types_tab);
                           FStar_TypeChecker_Env.enable_defer_to_tac =
                             (uu___3452_25652.FStar_TypeChecker_Env.enable_defer_to_tac)
                         }) t in
                    (match uu____25644 with
                     | (uu____25653, ty, uu____25655) ->
                         eta_expand_with_type env1 t ty)))
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___3464_25736 = x in
      let uu____25737 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3464_25736.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3464_25736.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25737
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25740 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25755 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25756 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25757 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25758 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25765 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25766 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25767 -> t1
    | FStar_Syntax_Syntax.Tm_unknown -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu___3490_25801 = rc in
          let uu____25802 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____25811 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3490_25801.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25802;
            FStar_Syntax_Syntax.residual_flags = uu____25811
          } in
        let uu____25814 =
          let uu____25815 =
            let uu____25834 = elim_delayed_subst_binders bs in
            let uu____25843 = elim_delayed_subst_term t2 in
            let uu____25846 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____25834, uu____25843, uu____25846) in
          FStar_Syntax_Syntax.Tm_abs uu____25815 in
        mk uu____25814
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____25883 =
          let uu____25884 =
            let uu____25899 = elim_delayed_subst_binders bs in
            let uu____25908 = elim_delayed_subst_comp c in
            (uu____25899, uu____25908) in
          FStar_Syntax_Syntax.Tm_arrow uu____25884 in
        mk uu____25883
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu____25927 =
          let uu____25928 =
            let uu____25935 = elim_bv bv in
            let uu____25936 = elim_delayed_subst_term phi in
            (uu____25935, uu____25936) in
          FStar_Syntax_Syntax.Tm_refine uu____25928 in
        mk uu____25927
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu____25967 =
          let uu____25968 =
            let uu____25985 = elim_delayed_subst_term t2 in
            let uu____25988 = elim_delayed_subst_args args in
            (uu____25985, uu____25988) in
          FStar_Syntax_Syntax.Tm_app uu____25968 in
        mk uu____25967
    | FStar_Syntax_Syntax.Tm_match (t2, branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3512_26060 = p in
              let uu____26061 =
                let uu____26062 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____26062 in
              {
                FStar_Syntax_Syntax.v = uu____26061;
                FStar_Syntax_Syntax.p =
                  (uu___3512_26060.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3516_26064 = p in
              let uu____26065 =
                let uu____26066 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____26066 in
              {
                FStar_Syntax_Syntax.v = uu____26065;
                FStar_Syntax_Syntax.p =
                  (uu___3516_26064.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___3522_26073 = p in
              let uu____26074 =
                let uu____26075 =
                  let uu____26082 = elim_bv x in
                  let uu____26083 = elim_delayed_subst_term t0 in
                  (uu____26082, uu____26083) in
                FStar_Syntax_Syntax.Pat_dot_term uu____26075 in
              {
                FStar_Syntax_Syntax.v = uu____26074;
                FStar_Syntax_Syntax.p =
                  (uu___3522_26073.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___3528_26106 = p in
              let uu____26107 =
                let uu____26108 =
                  let uu____26121 =
                    FStar_List.map
                      (fun uu____26144 ->
                         match uu____26144 with
                         | (x, b) ->
                             let uu____26157 = elim_pat x in (uu____26157, b))
                      pats in
                  (fv, uu____26121) in
                FStar_Syntax_Syntax.Pat_cons uu____26108 in
              {
                FStar_Syntax_Syntax.v = uu____26107;
                FStar_Syntax_Syntax.p =
                  (uu___3528_26106.FStar_Syntax_Syntax.p)
              }
          | uu____26170 -> p in
        let elim_branch uu____26194 =
          match uu____26194 with
          | (pat, wopt, t3) ->
              let uu____26220 = elim_pat pat in
              let uu____26223 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____26226 = elim_delayed_subst_term t3 in
              (uu____26220, uu____26223, uu____26226) in
        let uu____26231 =
          let uu____26232 =
            let uu____26255 = elim_delayed_subst_term t2 in
            let uu____26258 = FStar_List.map elim_branch branches1 in
            (uu____26255, uu____26258) in
          FStar_Syntax_Syntax.Tm_match uu____26232 in
        mk uu____26231
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let elim_ascription uu____26389 =
          match uu____26389 with
          | (tc, topt) ->
              let uu____26424 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26434 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____26434
                | FStar_Util.Inr c ->
                    let uu____26436 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____26436 in
              let uu____26437 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____26424, uu____26437) in
        let uu____26446 =
          let uu____26447 =
            let uu____26474 = elim_delayed_subst_term t2 in
            let uu____26477 = elim_ascription a in
            (uu____26474, uu____26477, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____26447 in
        mk uu____26446
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu___3558_26538 = lb in
          let uu____26539 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____26542 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3558_26538.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3558_26538.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26539;
            FStar_Syntax_Syntax.lbeff =
              (uu___3558_26538.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26542;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3558_26538.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3558_26538.FStar_Syntax_Syntax.lbpos)
          } in
        let uu____26545 =
          let uu____26546 =
            let uu____26559 =
              let uu____26566 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____26566) in
            let uu____26575 = elim_delayed_subst_term t2 in
            (uu____26559, uu____26575) in
          FStar_Syntax_Syntax.Tm_let uu____26546 in
        mk uu____26545
    | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
        mk (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi in
        let uu____26619 =
          let uu____26620 =
            let uu____26627 = elim_delayed_subst_term tm in
            (uu____26627, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu____26620 in
        mk uu____26619
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu____26638 =
          let uu____26639 =
            let uu____26646 = elim_delayed_subst_term t2 in
            let uu____26649 = elim_delayed_subst_meta md in
            (uu____26646, uu____26649) in
          FStar_Syntax_Syntax.Tm_meta uu____26639 in
        mk uu____26638
and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_List.map
      (fun uu___17_26658 ->
         match uu___17_26658 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26662 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____26662
         | f -> f) flags
and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c ->
    let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uopt) ->
        let uu____26685 =
          let uu____26686 =
            let uu____26695 = elim_delayed_subst_term t in
            (uu____26695, uopt) in
          FStar_Syntax_Syntax.Total uu____26686 in
        mk uu____26685
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uu____26712 =
          let uu____26713 =
            let uu____26722 = elim_delayed_subst_term t in
            (uu____26722, uopt) in
          FStar_Syntax_Syntax.GTotal uu____26713 in
        mk uu____26712
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3591_26731 = ct in
          let uu____26732 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____26735 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____26746 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3591_26731.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3591_26731.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26732;
            FStar_Syntax_Syntax.effect_args = uu____26735;
            FStar_Syntax_Syntax.flags = uu____26746
          } in
        mk (FStar_Syntax_Syntax.Comp ct1)
and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_26749 ->
    match uu___18_26749 with
    | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
        let uu____26784 =
          let uu____26805 = FStar_List.map elim_delayed_subst_term names in
          let uu____26814 = FStar_List.map elim_delayed_subst_args args in
          (uu____26805, uu____26814) in
        FStar_Syntax_Syntax.Meta_pattern uu____26784
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____26869 =
          let uu____26876 = elim_delayed_subst_term t in (m, uu____26876) in
        FStar_Syntax_Syntax.Meta_monadic uu____26869
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu____26888 =
          let uu____26897 = elim_delayed_subst_term t in
          (m1, m2, uu____26897) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26888
    | m -> m
and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list)
  =
  fun args ->
    FStar_List.map
      (fun uu____26930 ->
         match uu____26930 with
         | (t, q) ->
             let uu____26949 = elim_delayed_subst_term t in (uu____26949, q))
      args
and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun uu____26977 ->
         match uu____26977 with
         | (x, q) ->
             let uu____26996 =
               let uu___3617_26997 = x in
               let uu____26998 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3617_26997.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3617_26997.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26998
               } in
             (uu____26996, q)) bs
let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list *
            (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
            FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
            FStar_Util.either))
  =
  fun env1 ->
    fun univ_names ->
      fun binders ->
        fun tc ->
          let t =
            match (binders, tc) with
            | ([], FStar_Util.Inl t) -> t
            | ([], FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____27104, FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  c.FStar_Syntax_Syntax.pos
            | (uu____27136, FStar_Util.Inl t) ->
                let uu____27158 =
                  let uu____27159 =
                    let uu____27174 = FStar_Syntax_Syntax.mk_Total t in
                    (binders, uu____27174) in
                  FStar_Syntax_Syntax.Tm_arrow uu____27159 in
                FStar_Syntax_Syntax.mk uu____27158 t.FStar_Syntax_Syntax.pos in
          let uu____27187 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____27187 with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env1 t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____27219 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27292 ->
                    let uu____27293 =
                      let uu____27302 =
                        let uu____27303 = FStar_Syntax_Subst.compress t4 in
                        uu____27303.FStar_Syntax_Syntax.n in
                      (uu____27302, tc) in
                    (match uu____27293 with
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inr uu____27332) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inl uu____27379) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____27424, FStar_Util.Inl uu____27425) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____27456 -> failwith "Impossible") in
              (match uu____27219 with
               | (binders1, tc1) -> (univ_names1, binders1, tc1))
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list * FStar_Syntax_Syntax.term'
            FStar_Syntax_Syntax.syntax))
  =
  fun env1 ->
    fun univ_names ->
      fun binders ->
        fun t ->
          let uu____27593 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t) in
          match uu____27593 with
          | (univ_names1, binders1, tc) ->
              let uu____27667 = FStar_Util.left tc in
              (univ_names1, binders1, uu____27667)
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list * FStar_Syntax_Syntax.comp'
            FStar_Syntax_Syntax.syntax))
  =
  fun env1 ->
    fun univ_names ->
      fun binders ->
        fun c ->
          let uu____27720 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c) in
          match uu____27720 with
          | (univ_names1, binders1, tc) ->
              let uu____27794 = FStar_Util.right tc in
              (univ_names1, binders1, uu____27794)
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1 ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univ_names, binders, typ, lids, lids') ->
          let uu____27835 = elim_uvars_aux_t env1 univ_names binders typ in
          (match uu____27835 with
           | (univ_names1, binders1, typ1) ->
               let uu___3700_27875 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3700_27875.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3700_27875.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3700_27875.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3700_27875.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3700_27875.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
          let uu___3706_27890 = s in
          let uu____27891 =
            let uu____27892 =
              let uu____27901 = FStar_List.map (elim_uvars env1) sigs in
              (uu____27901, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____27892 in
          {
            FStar_Syntax_Syntax.sigel = uu____27891;
            FStar_Syntax_Syntax.sigrng =
              (uu___3706_27890.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3706_27890.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3706_27890.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3706_27890.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3706_27890.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univ_names, typ, lident, i, lids) ->
          let uu____27918 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____27918 with
           | (univ_names1, uu____27942, typ1) ->
               let uu___3720_27964 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3720_27964.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3720_27964.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3720_27964.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3720_27964.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3720_27964.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) ->
          let uu____27970 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____27970 with
           | (univ_names1, uu____27994, typ1) ->
               let uu___3731_28016 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3731_28016.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3731_28016.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3731_28016.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3731_28016.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3731_28016.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____28044 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____28044 with
                    | (opening, lbunivs) ->
                        let elim t =
                          let uu____28069 =
                            let uu____28070 =
                              let uu____28071 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env1 uu____28071 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28070 in
                          elim_delayed_subst_term uu____28069 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___3747_28074 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3747_28074.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3747_28074.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3747_28074.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3747_28074.FStar_Syntax_Syntax.lbpos)
                        })) in
          let uu___3750_28075 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3750_28075.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3750_28075.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3750_28075.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3750_28075.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3750_28075.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l, us, t) ->
          let uu____28083 = elim_uvars_aux_t env1 us [] t in
          (match uu____28083 with
           | (us1, uu____28107, t1) ->
               let uu___3761_28129 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3761_28129.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3761_28129.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3761_28129.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3761_28129.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3761_28129.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28131 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit in
          (match uu____28131 with
           | (univs, binders, uu____28150) ->
               let uu____28171 =
                 let uu____28176 = FStar_Syntax_Subst.univ_var_opening univs in
                 match uu____28176 with
                 | (univs_opening, univs1) ->
                     let uu____28199 =
                       FStar_Syntax_Subst.univ_var_closing univs1 in
                     (univs_opening, uu____28199) in
               (match uu____28171 with
                | (univs_opening, univs_closing) ->
                    let uu____28202 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____28208 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____28209 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____28208, uu____28209) in
                    (match uu____28202 with
                     | (b_opening, b_closing) ->
                         let n = FStar_List.length univs in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____28235 =
                           match uu____28235 with
                           | (us, t) ->
                               let n_us = FStar_List.length us in
                               let uu____28253 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____28253 with
                                | (us1, t1) ->
                                    let uu____28264 =
                                      let uu____28273 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____28278 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____28273, uu____28278) in
                                    (match uu____28264 with
                                     | (b_opening1, b_closing1) ->
                                         let uu____28301 =
                                           let uu____28310 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           let uu____28315 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           (uu____28310, uu____28315) in
                                         (match uu____28301 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28339 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28339 in
                                              let uu____28340 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2 in
                                              (match uu____28340 with
                                               | (uu____28367, uu____28368,
                                                  t3) ->
                                                   let t4 =
                                                     let uu____28391 =
                                                       let uu____28392 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28392 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28391 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____28401 =
                             elim_uvars_aux_t env1 univs binders t in
                           match uu____28401 with
                           | (uu____28420, uu____28421, t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____28497 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____28524 =
                               let uu____28525 =
                                 FStar_Syntax_Subst.compress body in
                               uu____28525.FStar_Syntax_Syntax.n in
                             match uu____28524 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,
                                  (FStar_Util.Inl typ,
                                   FStar_Pervasives_Native.None),
                                  FStar_Pervasives_Native.None)
                                 -> (defn, typ)
                             | uu____28584 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____28617 =
                               let uu____28618 =
                                 FStar_Syntax_Subst.compress t in
                               uu____28618.FStar_Syntax_Syntax.n in
                             match uu____28617 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars, body, uu____28641) ->
                                 let uu____28666 = destruct_action_body body in
                                 (match uu____28666 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu____28715 ->
                                 let uu____28716 = destruct_action_body t in
                                 (match uu____28716 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu____28771 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____28771 with
                           | (action_univs, t) ->
                               let uu____28780 = destruct_action_typ_templ t in
                               (match uu____28780 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      let uu___3845_28827 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3845_28827.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3845_28827.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___3848_28829 = ed in
                           let uu____28830 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature in
                           let uu____28831 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu____28832 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3848_28829.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3848_28829.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____28830;
                             FStar_Syntax_Syntax.combinators = uu____28831;
                             FStar_Syntax_Syntax.actions = uu____28832;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3848_28829.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let uu___3851_28835 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3851_28835.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3851_28835.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3851_28835.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3851_28835.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3851_28835.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_28856 =
            match uu___19_28856 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu____28887 = elim_uvars_aux_t env1 us [] t in
                (match uu____28887 with
                 | (us1, uu____28919, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___3866_28950 = sub_eff in
            let uu____28951 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____28954 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___3866_28950.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3866_28950.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28951;
              FStar_Syntax_Syntax.lift = uu____28954
            } in
          let uu___3869_28957 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3869_28957.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3869_28957.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3869_28957.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3869_28957.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3869_28957.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, univ_names, binders, comp, flags) ->
          let uu____28967 = elim_uvars_aux_c env1 univ_names binders comp in
          (match uu____28967 with
           | (univ_names1, binders1, comp1) ->
               let uu___3882_29007 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3882_29007.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3882_29007.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3882_29007.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3882_29007.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3882_29007.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29010 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____29011 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29022 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m, n, p, (us_t, t), (us_ty, ty)) ->
          let uu____29052 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____29052 with
           | (us_t1, uu____29076, t1) ->
               let uu____29098 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____29098 with
                | (us_ty1, uu____29122, ty1) ->
                    let uu___3909_29144 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3909_29144.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3909_29144.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3909_29144.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3909_29144.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3909_29144.FStar_Syntax_Syntax.sigopts)
                    }))
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          (m, n, (us_t, t), (us_ty, ty)) ->
          let uu____29175 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____29175 with
           | (us_t1, uu____29199, t1) ->
               let uu____29221 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____29221 with
                | (us_ty1, uu____29245, ty1) ->
                    let uu___3929_29267 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                           (m, n, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3929_29267.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3929_29267.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3929_29267.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3929_29267.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3929_29267.FStar_Syntax_Syntax.sigopts)
                    }))
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env1 t
let (unfold_head_once :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let aux f us args =
        let uu____29316 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu____29316 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____29338 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
            (match uu____29338 with
             | (uu____29345, head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     t.FStar_Syntax_Syntax.pos in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env1 t' in
                 FStar_Pervasives_Native.Some t'1) in
      let uu____29349 = FStar_Syntax_Util.head_and_args t in
      match uu____29349 with
      | (head, args) ->
          let uu____29394 =
            let uu____29395 = FStar_Syntax_Subst.compress head in
            uu____29395.FStar_Syntax_Syntax.n in
          (match uu____29394 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____29402;
                  FStar_Syntax_Syntax.vars = uu____29403;_},
                us)
               -> aux fv us args
           | uu____29409 -> FStar_Pervasives_Native.None)
let (get_n_binders :
  FStar_TypeChecker_Env.env ->
    Prims.int ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.binder Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun env1 ->
    fun n ->
      fun t ->
        let rec aux retry n1 t1 =
          let uu____29465 = FStar_Syntax_Util.arrow_formals_comp t1 in
          match uu____29465 with
          | (bs, c) ->
              let len = FStar_List.length bs in
              (match (bs, c) with
               | ([], uu____29501) when retry ->
                   let uu____29520 = unfold_whnf env1 t1 in
                   aux false n1 uu____29520
               | ([], uu____29521) when Prims.op_Negation retry -> (bs, c)
               | (bs1, c1) when len = n1 -> (bs1, c1)
               | (bs1, c1) when len > n1 ->
                   let uu____29588 = FStar_List.splitAt n1 bs1 in
                   (match uu____29588 with
                    | (bs_l, bs_r) ->
                        let uu____29655 =
                          let uu____29656 = FStar_Syntax_Util.arrow bs_r c1 in
                          FStar_Syntax_Syntax.mk_Total uu____29656 in
                        (bs_l, uu____29655))
               | (bs1, c1) when
                   ((len < n1) && (FStar_Syntax_Util.is_total_comp c1)) &&
                     (let uu____29682 = FStar_Syntax_Util.has_decreases c1 in
                      Prims.op_Negation uu____29682)
                   ->
                   let uu____29683 =
                     aux true (n1 - len) (FStar_Syntax_Util.comp_result c1) in
                   (match uu____29683 with
                    | (bs', c') -> ((FStar_List.append bs1 bs'), c'))
               | (bs1, c1) -> (bs1, c1)) in
        aux true n t