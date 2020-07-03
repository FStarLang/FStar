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
           let uu____6254 =
             let uu____6269 = FStar_TypeChecker_Cfg.cfg_env cfg in
             uu____6269.FStar_TypeChecker_Env.nbe in
           uu____6254 s cfg.FStar_TypeChecker_Cfg.tcenv tm in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6273 ->
              let uu____6274 = FStar_Syntax_Print.term_to_string tm_norm in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6274);
         tm_norm)
let firstn :
  'uuuuuu6281 .
    Prims.int ->
      'uuuuuu6281 Prims.list ->
        ('uuuuuu6281 Prims.list * 'uuuuuu6281 Prims.list)
  =
  fun k ->
    fun l ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg ->
    fun stack1 ->
      let rec drop_irrel uu___11_6332 =
        match uu___11_6332 with
        | (MemoLazy uu____6337)::s -> drop_irrel s
        | (UnivArgs uu____6347)::s -> drop_irrel s
        | s -> s in
      let uu____6360 = drop_irrel stack1 in
      match uu____6360 with
      | (App
          (uu____6363,
           {
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify);
             FStar_Syntax_Syntax.pos = uu____6364;
             FStar_Syntax_Syntax.vars = uu____6365;_},
           uu____6366, uu____6367))::uu____6368
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6373 -> false
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t, uu____6396) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t, uu____6406) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6427 ->
                  match uu____6427 with
                  | (a, uu____6437) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args) in
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6447 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6462 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6463 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6476 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6477 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6478 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6479 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6480 -> false
    | FStar_Syntax_Syntax.Tm_unknown -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6481 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6488 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6495 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6508 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6527 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6542 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6549 -> true
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6619 ->
                   match uu____6619 with
                   | (a, uu____6629) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____6640) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____6735, args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____6790 ->
                        match uu____6790 with
                        | (a, uu____6800) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6809, uu____6810, t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6816, t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6822 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6829 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6830 -> false))
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_no -> true | uu____6836 -> false
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_yes -> true | uu____6842 -> false
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_fully -> true | uu____6848 -> false
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_reify -> true | uu____6854 -> false
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
            let uu____6883 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
            match uu____6883 with
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
              (fun uu____7011 ->
                 fun uu____7012 ->
                   match (uu____7011, uu____7012) with
                   | ((a, b, c), (x, y, z)) -> ((a || x), (b || y), (c || z)))
              l (false, false, false) in
          let string_of_res uu____7072 =
            match uu____7072 with
            | (x, y, z) ->
                let uu____7082 = FStar_Util.string_of_bool x in
                let uu____7083 = FStar_Util.string_of_bool y in
                let uu____7084 = FStar_Util.string_of_bool z in
                FStar_Util.format3 "(%s,%s,%s)" uu____7082 uu____7083
                  uu____7084 in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7103 ->
                    let uu____7104 = FStar_Syntax_Print.fv_to_string fv in
                    let uu____7105 = FStar_Util.string_of_bool b in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7104 uu____7105);
               if b then reif else no)
            else
              if
                (let uu____7113 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                 FStar_Option.isSome uu____7113)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7118 ->
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
                          ((is_rec, uu____7152), uu____7153);
                        FStar_Syntax_Syntax.sigrng = uu____7154;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7156;
                        FStar_Syntax_Syntax.sigattrs = uu____7157;
                        FStar_Syntax_Syntax.sigopts = uu____7158;_},
                      uu____7159),
                     uu____7160),
                    uu____7161, uu____7162, uu____7163) when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7270 ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7271, uu____7272, uu____7273, uu____7274) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7341 ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec, uu____7343), uu____7344);
                        FStar_Syntax_Syntax.sigrng = uu____7345;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7347;
                        FStar_Syntax_Syntax.sigattrs = uu____7348;
                        FStar_Syntax_Syntax.sigopts = uu____7349;_},
                      uu____7350),
                     uu____7351),
                    uu____7352, uu____7353, uu____7354) when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7461 ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____7462, FStar_Pervasives_Native.Some uu____7463,
                    uu____7464, uu____7465) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7533 ->
                           let uu____7534 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7534);
                      (let uu____7535 =
                         let uu____7544 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7564 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____7564 in
                         let uu____7571 =
                           let uu____7580 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7600 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____7600 in
                           let uu____7611 =
                             let uu____7620 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7640 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____7640 in
                             [uu____7620] in
                           uu____7580 :: uu____7611 in
                         uu____7544 :: uu____7571 in
                       comb_or uu____7535))
                 | (uu____7671, uu____7672, FStar_Pervasives_Native.Some
                    uu____7673, uu____7674) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7742 ->
                           let uu____7743 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7743);
                      (let uu____7744 =
                         let uu____7753 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7773 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____7773 in
                         let uu____7780 =
                           let uu____7789 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7809 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____7809 in
                           let uu____7820 =
                             let uu____7829 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7849 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____7849 in
                             [uu____7829] in
                           uu____7789 :: uu____7820 in
                         uu____7753 :: uu____7780 in
                       comb_or uu____7744))
                 | (uu____7880, uu____7881, uu____7882,
                    FStar_Pervasives_Native.Some uu____7883) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7951 ->
                           let uu____7952 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7952);
                      (let uu____7953 =
                         let uu____7962 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7982 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____7982 in
                         let uu____7989 =
                           let uu____7998 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8018 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8018 in
                           let uu____8029 =
                             let uu____8038 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8058 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8058 in
                             [uu____8038] in
                           uu____7998 :: uu____8029 in
                         uu____7962 :: uu____7989 in
                       comb_or uu____7953))
                 | uu____8089 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8135 ->
                           let uu____8136 =
                             FStar_Syntax_Print.fv_to_string fv in
                           let uu____8137 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta in
                           let uu____8138 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8136 uu____8137 uu____8138);
                      (let uu____8139 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_8143 ->
                                 match uu___12_8143 with
                                 | FStar_TypeChecker_Env.NoDelta -> false
                                 | FStar_TypeChecker_Env.InliningDelta ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                     -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8145 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8145 l)) in
                       FStar_All.pipe_left yesno uu____8139))) in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8157 ->
               let uu____8158 = FStar_Syntax_Print.fv_to_string fv in
               let uu____8159 =
                 let uu____8160 = FStar_Syntax_Syntax.range_of_fv fv in
                 FStar_Range.string_of_range uu____8160 in
               let uu____8161 = string_of_res res in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8158 uu____8159 uu____8161);
          (match res with
           | (false, uu____8162, uu____8163) -> Should_unfold_no
           | (true, false, false) -> Should_unfold_yes
           | (true, true, false) -> Should_unfold_fully
           | (true, false, true) -> Should_unfold_reify
           | uu____8164 ->
               let uu____8171 =
                 let uu____8172 = string_of_res res in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____8172 in
               FStar_All.pipe_left failwith uu____8171)
let decide_unfolding :
  'uuuuuu8187 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu8187 ->
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
                    let uu___1168_8256 = cfg in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1170_8259 = cfg.FStar_TypeChecker_Cfg.steps in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1170_8259.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1170_8259.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1168_8256.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____8321 = push e t in (UnivArgs (us, r)) ::
                          uu____8321
                    | h::t -> e :: h :: t in
                  let ref =
                    let uu____8333 =
                      let uu____8334 =
                        let uu____8335 = FStar_Syntax_Syntax.lid_of_fv fv in
                        FStar_Const.Const_reflect uu____8335 in
                      FStar_Syntax_Syntax.Tm_constant uu____8334 in
                    FStar_Syntax_Syntax.mk uu____8333 FStar_Range.dummyRange in
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
    let uu____8378 =
      let uu____8379 = FStar_Syntax_Subst.compress t in
      uu____8379.FStar_Syntax_Syntax.n in
    match uu____8378 with
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu____8410 =
          let uu____8411 = FStar_Syntax_Util.un_uinst hd in
          uu____8411.FStar_Syntax_Syntax.n in
        (match uu____8410 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____8426 =
                 let uu____8433 =
                   let uu____8444 = FStar_All.pipe_right args FStar_List.tl in
                   FStar_All.pipe_right uu____8444 FStar_List.tl in
                 FStar_All.pipe_right uu____8433 FStar_List.hd in
               FStar_All.pipe_right uu____8426 FStar_Pervasives_Native.fst in
             FStar_Pervasives_Native.Some f
         | uu____8543 -> FStar_Pervasives_Native.None)
    | uu____8544 -> FStar_Pervasives_Native.None
let (is_partial_primop_app :
  FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun cfg ->
    fun t ->
      let uu____8555 = FStar_Syntax_Util.head_and_args t in
      match uu____8555 with
      | (hd, args) ->
          let uu____8598 =
            let uu____8599 = FStar_Syntax_Util.un_uinst hd in
            uu____8599.FStar_Syntax_Syntax.n in
          (match uu____8598 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____8603 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
               (match uu____8603 with
                | FStar_Pervasives_Native.Some prim_step ->
                    prim_step.FStar_TypeChecker_Cfg.arity >
                      (FStar_List.length args)
                | FStar_Pervasives_Native.None -> false)
           | uu____8615 -> false)
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8892 ->
                   let uu____8907 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8907
               | uu____8908 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8917 ->
               let uu____8918 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____8919 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm in
               let uu____8920 = FStar_Syntax_Print.term_to_string t1 in
               let uu____8921 =
                 FStar_Util.string_of_int (FStar_List.length env1) in
               let uu____8928 =
                 let uu____8929 =
                   let uu____8932 = firstn (Prims.of_int (4)) stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8932 in
                 stack_to_string uu____8929 in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8918 uu____8919 uu____8920 uu____8921 uu____8928);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8958 ->
               let uu____8959 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8959);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8963 ->
                     let uu____8964 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8964);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8965 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8969 ->
                     let uu____8970 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8970);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____8971 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8975 ->
                     let uu____8976 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8976);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8977 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8981 ->
                     let uu____8982 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8982);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8983;
                 FStar_Syntax_Syntax.fv_delta = uu____8984;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8988 ->
                     let uu____8989 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8989);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8990;
                 FStar_Syntax_Syntax.fv_delta = uu____8991;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8992);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9002 ->
                     let uu____9003 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9003);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid in
               let uu____9007 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo in
               (match uu____9007 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____9010)
                    when uu____9010 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9014 ->
                          let uu____9015 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9015);
                     rebuild cfg env1 stack1 t1)
                | uu____9016 ->
                    let uu____9019 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo in
                    (match uu____9019 with
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
               let uu____9058 = closure_as_term cfg env1 t2 in
               rebuild cfg env1 stack1 uu____9058
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9086 = is_norm_request hd args in
                  uu____9086 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9089 = rejig_norm_request hd args in
                 norm cfg env1 stack1 uu____9089))
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9117 = is_norm_request hd args in
                  uu____9117 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1292_9121 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1294_9124 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1294_9124.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1292_9121.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1292_9121.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1292_9121.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1292_9121.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1292_9121.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1292_9121.FStar_TypeChecker_Cfg.reifying)
                   } in
                 let uu____9129 =
                   get_norm_request cfg (norm cfg' env1 []) args in
                 match uu____9129 with
                 | FStar_Pervasives_Native.None ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____9162 ->
                                 fun stack2 ->
                                   match uu____9162 with
                                   | (a, aq) ->
                                       let uu____9174 =
                                         let uu____9175 =
                                           let uu____9182 =
                                             let uu____9183 =
                                               let uu____9214 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None in
                                               (env1, a, uu____9214, false) in
                                             Clos uu____9183 in
                                           (uu____9182, aq,
                                             (t1.FStar_Syntax_Syntax.pos)) in
                                         Arg uu____9175 in
                                       uu____9174 :: stack2) args) in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____9280 ->
                            let uu____9281 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____9281);
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
                         let uu____9308 =
                           let uu____9309 =
                             let uu____9310 = FStar_Util.time_diff start fin in
                             FStar_Pervasives_Native.snd uu____9310 in
                           FStar_Util.string_of_int uu____9309 in
                         let uu____9315 =
                           FStar_Syntax_Print.term_to_string tm' in
                         let uu____9316 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1 in
                         let uu____9317 =
                           FStar_Syntax_Print.term_to_string tm_norm in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____9308 uu____9315 uu____9316 uu____9317)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s, tm) ->
                     let delta_level =
                       let uu____9334 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_9339 ->
                                 match uu___13_9339 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____9340 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____9341 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____9344 -> true
                                 | uu____9347 -> false)) in
                       if uu____9334
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta] in
                     let cfg'1 =
                       let uu___1332_9352 = cfg in
                       let uu____9353 =
                         let uu___1334_9354 =
                           FStar_TypeChecker_Cfg.to_fsteps s in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1334_9354.FStar_TypeChecker_Cfg.for_extraction)
                         } in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____9353;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1332_9352.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1332_9352.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1332_9352.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1332_9352.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1332_9352.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1332_9352.FStar_TypeChecker_Cfg.reifying)
                       } in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1 in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____9359 =
                           let uu____9360 =
                             let uu____9365 = FStar_Util.now () in
                             (tm, uu____9365) in
                           Debug uu____9360 in
                         uu____9359 :: tail
                       else tail in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u in
               let uu____9369 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____9369
           | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____9378 =
                      let uu____9385 =
                        FStar_List.map (norm_universe cfg env1) us in
                      (uu____9385, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____9378 in
                  let stack2 = us1 :: stack1 in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____9394 = lookup_bvar env1 x in
               (match uu____9394 with
                | Univ uu____9395 ->
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
                      let uu____9444 = FStar_ST.op_Bang r in
                      (match uu____9444 with
                       | FStar_Pervasives_Native.Some (env3, t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9527 ->
                                 let uu____9528 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____9529 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9528
                                   uu____9529);
                            (let uu____9530 = maybe_weakly_reduced t' in
                             if uu____9530
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____9531 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
               (match stack1 with
                | (UnivArgs uu____9573)::uu____9574 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c, uu____9584, uu____9585))::stack_rest ->
                    (match c with
                     | Univ uu____9589 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____9598 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9627 ->
                                    let uu____9628 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9628);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9662 ->
                                    let uu____9663 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9663);
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
                       (fun uu____9709 ->
                          let uu____9710 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9710);
                     norm cfg env1 stack2 t1)
                | (Match uu____9711)::uu____9712 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____9725 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____9725 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____9761 -> dummy :: env2) env1) in
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
                                          let uu____9804 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____9804)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_9811 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_9811.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_9811.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9812 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9818 ->
                                 let uu____9819 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9819);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_9830 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_9830.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____9833)::uu____9834 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____9843 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____9843 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____9879 -> dummy :: env2) env1) in
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
                                          let uu____9922 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____9922)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_9929 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_9929.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_9929.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9930 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9936 ->
                                 let uu____9937 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9937);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_9948 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_9948.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____9951)::uu____9952 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____9963 = FStar_Syntax_Subst.open_term' bs body in
                       match uu____9963 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____9999 -> dummy :: env2) env1) in
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
                                          let uu____10042 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10042)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10049 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10049.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10049.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10050 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10056 ->
                                 let uu____10057 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10057);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10068 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10068.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____10071)::uu____10072 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10085 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10085 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10121 -> dummy :: env2) env1) in
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
                                          let uu____10164 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10164)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10171 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10171.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10171.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10172 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10178 ->
                                 let uu____10179 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10179);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10190 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10190.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____10193)::uu____10194 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10207 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10207 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10243 -> dummy :: env2) env1) in
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
                                          let uu____10286 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10286)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10293 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10293.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10293.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10294 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10300 ->
                                 let uu____10301 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10301);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10312 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10312.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____10315)::uu____10316 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10329 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10329 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10365 -> dummy :: env2) env1) in
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
                                          let uu____10408 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10408)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10415 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10415.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10415.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10416 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10422 ->
                                 let uu____10423 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10423);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10434 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10434.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____10437)::uu____10438 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10455 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10455 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10491 -> dummy :: env2) env1) in
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
                                          let uu____10534 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10534)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10541 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10541.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10541.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10542 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10548 ->
                                 let uu____10549 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10549);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10560 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10560.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____10565 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10565 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10601 -> dummy :: env2) env1) in
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
                                          let uu____10644 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10644)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10651 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10651.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10651.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10652 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10658 ->
                                 let uu____10659 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10659);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10670 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10670.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head, args) ->
               let strict_args =
                 let uu____10704 =
                   let uu____10705 = FStar_Syntax_Util.un_uinst head in
                   uu____10705.FStar_Syntax_Syntax.n in
                 match uu____10704 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____10713 -> FStar_Pervasives_Native.None in
               (match strict_args with
                | FStar_Pervasives_Native.None ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____10732 ->
                              fun stack2 ->
                                match uu____10732 with
                                | (a, aq) ->
                                    let uu____10744 =
                                      let uu____10745 =
                                        let uu____10752 =
                                          let uu____10753 =
                                            let uu____10784 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu____10784, false) in
                                          Clos uu____10753 in
                                        (uu____10752, aq,
                                          (t1.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____10745 in
                                    uu____10744 :: stack2) args) in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10850 ->
                          let uu____10851 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args) in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10851);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____10896 ->
                              match uu____10896 with
                              | (a, i) ->
                                  let uu____10907 = norm cfg env1 [] a in
                                  (uu____10907, i))) in
                    let norm_args_len = FStar_List.length norm_args in
                    let uu____10913 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____10919 = FStar_List.nth norm_args i in
                                 match uu____10919 with
                                 | (arg_i, uu____10929) ->
                                     let uu____10930 =
                                       FStar_Syntax_Util.head_and_args arg_i in
                                     (match uu____10930 with
                                      | (head1, uu____10948) ->
                                          let uu____10973 =
                                            let uu____10974 =
                                              FStar_Syntax_Util.un_uinst
                                                head1 in
                                            uu____10974.FStar_Syntax_Syntax.n in
                                          (match uu____10973 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____10977 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____10979 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____10979
                                           | uu____10980 -> false))))) in
                    if uu____10913
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____10995 ->
                                fun stack2 ->
                                  match uu____10995 with
                                  | (a, aq) ->
                                      let uu____11007 =
                                        let uu____11008 =
                                          let uu____11015 =
                                            let uu____11016 =
                                              let uu____11047 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a)) in
                                              (env1, a, uu____11047, false) in
                                            Clos uu____11016 in
                                          (uu____11015, aq,
                                            (t1.FStar_Syntax_Syntax.pos)) in
                                        Arg uu____11008 in
                                      uu____11007 :: stack2) norm_args) in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____11127 ->
                            let uu____11128 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____11128);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x, uu____11141) when
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
                             ((let uu___1525_11185 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1525_11185.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1525_11185.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2
                  | uu____11186 ->
                      let uu____11201 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 uu____11201)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
                  let uu____11204 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____11204 with
                  | (closing, f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1 in
                      let t2 =
                        let uu____11235 =
                          let uu____11236 =
                            let uu____11243 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___1534_11249 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1534_11249.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1534_11249.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11243) in
                          FStar_Syntax_Syntax.Tm_refine uu____11236 in
                        FStar_Syntax_Syntax.mk uu____11235
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____11272 = closure_as_term cfg env1 t1 in
                 rebuild cfg env1 stack1 uu____11272
               else
                 (let uu____11274 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____11274 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu____11282 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2 -> fun uu____11308 -> dummy :: env2)
                               env1) in
                        norm_comp cfg uu____11282 c1 in
                      let t2 =
                        let uu____11332 = norm_binders cfg env1 bs1 in
                        FStar_Syntax_Util.arrow uu____11332 c2 in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) ->
               (match stack1 with
                | (Match uu____11445)::uu____11446 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11459 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____11460)::uu____11461 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11472 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____11473,
                     {
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify);
                       FStar_Syntax_Syntax.pos = uu____11474;
                       FStar_Syntax_Syntax.vars = uu____11475;_},
                     uu____11476, uu____11477))::uu____11478
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11485 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____11486)::uu____11487 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11498 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____11499 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11502 ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11 in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____11506 ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11531 = norm cfg env1 [] t2 in
                             FStar_Util.Inl uu____11531
                         | FStar_Util.Inr c ->
                             let uu____11545 = norm_comp cfg env1 c in
                             FStar_Util.Inr uu____11545 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 []) in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____11568 =
                               let uu____11569 =
                                 let uu____11596 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____11596, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11569 in
                             FStar_Syntax_Syntax.mk uu____11568
                               t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env1 stack2 t2
                       | uu____11631 ->
                           let uu____11632 =
                             let uu____11633 =
                               let uu____11634 =
                                 let uu____11661 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____11661, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11634 in
                             FStar_Syntax_Syntax.mk uu____11633
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env1 stack1 uu____11632))))
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
                   let uu___1613_11738 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1615_11741 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1615_11741.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1613_11738.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____11777 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____11777 with
                         | (openings, lbunivs) ->
                             let cfg1 =
                               let uu___1628_11797 = cfg in
                               let uu____11798 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____11798;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1628_11797.FStar_TypeChecker_Cfg.reifying)
                               } in
                             let norm1 t2 =
                               let uu____11805 =
                                 let uu____11806 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env1 [] uu____11806 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11805 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___1635_11809 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1635_11809.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1635_11809.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1635_11809.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1635_11809.FStar_Syntax_Syntax.lbpos)
                             })) in
               let uu____11810 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____11810
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11821,
                 { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____11822;
                   FStar_Syntax_Syntax.lbunivs = uu____11823;
                   FStar_Syntax_Syntax.lbtyp = uu____11824;
                   FStar_Syntax_Syntax.lbeff = uu____11825;
                   FStar_Syntax_Syntax.lbdef = uu____11826;
                   FStar_Syntax_Syntax.lbattrs = uu____11827;
                   FStar_Syntax_Syntax.lbpos = uu____11828;_}::uu____11829),
                uu____11830)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
               let uu____11869 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb in
               if uu____11869
               then
                 let binder =
                   let uu____11871 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____11871 in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef in
                 let env2 =
                   let uu____11882 =
                     let uu____11889 =
                       let uu____11890 =
                         let uu____11921 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env1, def, uu____11921, false) in
                       Clos uu____11890 in
                     ((FStar_Pervasives_Native.Some binder), uu____11889) in
                   uu____11882 :: env1 in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11994 ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____11996 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____11998 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff in
                       FStar_Syntax_Util.is_div_effect uu____11998) in
                  if uu____11996
                  then
                    let ffun =
                      let uu____12002 =
                        let uu____12003 =
                          let uu____12022 =
                            let uu____12031 =
                              let uu____12038 =
                                FStar_All.pipe_right
                                  lb.FStar_Syntax_Syntax.lbname
                                  FStar_Util.left in
                              FStar_Syntax_Syntax.mk_binder uu____12038 in
                            [uu____12031] in
                          (uu____12022, body, FStar_Pervasives_Native.None) in
                        FStar_Syntax_Syntax.Tm_abs uu____12003 in
                      FStar_Syntax_Syntax.mk uu____12002
                        t1.FStar_Syntax_Syntax.pos in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12072 ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12076 ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____12077 = closure_as_term cfg env1 t1 in
                        rebuild cfg env1 stack1 uu____12077))
                    else
                      (let uu____12079 =
                         let uu____12084 =
                           let uu____12085 =
                             let uu____12092 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left in
                             FStar_All.pipe_right uu____12092
                               FStar_Syntax_Syntax.mk_binder in
                           [uu____12085] in
                         FStar_Syntax_Subst.open_term uu____12084 body in
                       match uu____12079 with
                       | (bs, body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____12119 ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                             let lbname =
                               let x =
                                 let uu____12127 = FStar_List.hd bs in
                                 FStar_Pervasives_Native.fst uu____12127 in
                               FStar_Util.Inl
                                 (let uu___1682_12143 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1682_12143.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1682_12143.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }) in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____12146 ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1687_12148 = lb in
                                let uu____12149 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef in
                                let uu____12152 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1687_12148.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1687_12148.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____12149;
                                  FStar_Syntax_Syntax.lbattrs = uu____12152;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1687_12148.FStar_Syntax_Syntax.lbpos)
                                } in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2 ->
                                        fun uu____12187 -> dummy :: env2)
                                     env1) in
                              let stack2 = (Cfg cfg) :: stack1 in
                              let cfg1 =
                                let uu___1694_12212 = cfg in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1694_12212.FStar_TypeChecker_Cfg.reifying)
                                } in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____12215 ->
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
               let uu____12232 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____12232 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____12268 =
                               let uu___1710_12269 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1710_12269.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1710_12269.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____12268 in
                           let uu____12270 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____12270 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env1 xs in
                               let env2 =
                                 let uu____12296 =
                                   FStar_List.map (fun uu____12318 -> dummy)
                                     xs1 in
                                 let uu____12325 =
                                   let uu____12334 =
                                     FStar_List.map
                                       (fun uu____12350 -> dummy) lbs1 in
                                   FStar_List.append uu____12334 env1 in
                                 FStar_List.append uu____12296 uu____12325 in
                               let def_body1 = norm cfg env2 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12370 =
                                       let uu___1724_12371 = rc in
                                       let uu____12372 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1724_12371.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12372;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1724_12371.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____12370
                                 | uu____12381 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___1729_12387 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1729_12387.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1729_12387.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1729_12387.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1729_12387.FStar_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu____12397 =
                        FStar_List.map (fun uu____12413 -> dummy) lbs2 in
                      FStar_List.append uu____12397 env1 in
                    let body2 = norm cfg env' [] body1 in
                    let uu____12421 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____12421 with
                     | (lbs3, body3) ->
                         let t2 =
                           let uu___1738_12437 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1738_12437.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1738_12437.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs, body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____12466 = closure_as_term cfg env1 t1 in
               rebuild cfg env1 stack1 uu____12466
           | FStar_Syntax_Syntax.Tm_let (lbs, body) ->
               let uu____12485 =
                 FStar_List.fold_right
                   (fun lb ->
                      fun uu____12561 ->
                        match uu____12561 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___1754_12682 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1754_12682.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1754_12682.FStar_Syntax_Syntax.sort)
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
               (match uu____12485 with
                | (rec_env, memos, uu____12865) ->
                    let uu____12918 =
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
                             let uu____13101 =
                               let uu____13108 =
                                 let uu____13109 =
                                   let uu____13140 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13140, false) in
                                 Clos uu____13109 in
                               (FStar_Pervasives_Native.None, uu____13108) in
                             uu____13101 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1 in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head, m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____13222 ->
                     let uu____13223 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13223);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1, t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13245 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____13247::uu____13248 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l, r, uu____13253) ->
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
                             | uu____13328 -> norm cfg env1 stack1 head)
                        | [] ->
                            let head1 = norm cfg env1 [] head in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names, args) ->
                                  let names1 =
                                    FStar_All.pipe_right names
                                      (FStar_List.map (norm cfg env1 [])) in
                                  let uu____13376 =
                                    let uu____13397 =
                                      norm_pattern_args cfg env1 args in
                                    (names1, uu____13397) in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13376
                              | uu____13426 -> m in
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13432 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13448 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13462 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____13475 =
                        let uu____13476 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____13477 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13476 uu____13477 in
                      failwith uu____13475
                    else
                      (let uu____13479 = inline_closure_env cfg env1 [] t2 in
                       rebuild cfg env1 stack1 uu____13479)
                | uu____13480 -> norm cfg env1 stack1 t2))
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
              let uu____13489 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu____13489 with
              | FStar_Pervasives_Native.None ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____13503 ->
                        let uu____13504 = FStar_Syntax_Print.fv_to_string f in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____13504);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us, t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____13515 ->
                        let uu____13516 =
                          FStar_Syntax_Print.term_to_string t0 in
                        let uu____13517 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____13516 uu____13517);
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
                      | (UnivArgs (us', uu____13524))::stack2 ->
                          ((let uu____13533 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm") in
                            if uu____13533
                            then
                              FStar_List.iter
                                (fun x ->
                                   let uu____13537 =
                                     FStar_Syntax_Print.univ_to_string x in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____13537) us'
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
                      | uu____13570 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____13573 ->
                          let uu____13576 =
                            let uu____13577 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13577 in
                          failwith uu____13576
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
              let uu____13594 =
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
                    let uu___1865_13611 = cfg in
                    let uu____13612 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____13612;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1865_13611.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1865_13611.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1865_13611.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1865_13611.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1865_13611.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1865_13611.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1865_13611.FStar_TypeChecker_Cfg.reifying)
                    } in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1) in
              match uu____13594 with
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
                     (uu____13652,
                      {
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify);
                        FStar_Syntax_Syntax.pos = uu____13653;
                        FStar_Syntax_Syntax.vars = uu____13654;_},
                      uu____13655, uu____13656))::uu____13657
                     -> ()
                 | uu____13662 ->
                     let uu____13665 =
                       let uu____13666 = stack_to_string stack1 in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____13666 in
                     failwith uu____13665);
                (let top0 = top in
                 let top1 = FStar_Syntax_Util.unascribe top in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____13673 ->
                      let uu____13674 = FStar_Syntax_Print.tag_of_term top1 in
                      let uu____13675 =
                        FStar_Syntax_Print.term_to_string top1 in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____13674
                        uu____13675);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1 in
                  let uu____13677 =
                    let uu____13678 = FStar_Syntax_Subst.compress top2 in
                    uu____13678.FStar_Syntax_Syntax.n in
                  match uu____13677 with
                  | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name in
                      let uu____13697 =
                        let uu____13706 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr in
                        FStar_All.pipe_right uu____13706 FStar_Util.must in
                      (match uu____13697 with
                       | (uu____13721, repr) ->
                           let uu____13731 =
                             let uu____13738 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr in
                             FStar_All.pipe_right uu____13738 FStar_Util.must in
                           (match uu____13731 with
                            | (uu____13775, bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____13781 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____13791 =
                                         let uu____13792 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____13792.FStar_Syntax_Syntax.n in
                                       match uu____13791 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,
                                            FStar_Syntax_Syntax.Meta_monadic
                                            (uu____13798, uu____13799))
                                           ->
                                           let uu____13808 =
                                             let uu____13809 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____13809.FStar_Syntax_Syntax.n in
                                           (match uu____13808 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,
                                                 FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____13815, msrc,
                                                  uu____13817))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____13826 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13826
                                            | uu____13827 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____13828 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____13829 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____13829 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1944_13834 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1944_13834.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1944_13834.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1944_13834.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1944_13834.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1944_13834.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let uu____13835 =
                                            FStar_List.tl stack1 in
                                          let uu____13836 =
                                            let uu____13837 =
                                              let uu____13838 =
                                                let uu____13851 =
                                                  FStar_Syntax_Util.mk_reify
                                                    body in
                                                ((false, [lb1]), uu____13851) in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu____13838 in
                                            FStar_Syntax_Syntax.mk
                                              uu____13837
                                              top2.FStar_Syntax_Syntax.pos in
                                          norm cfg env1 uu____13835
                                            uu____13836
                                      | FStar_Pervasives_Native.None ->
                                          let uu____13864 =
                                            let uu____13865 = is_return body in
                                            match uu____13865 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____13869;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____13870;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____13873 -> false in
                                          if uu____13864
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
                                               let uu____13898 =
                                                 let uu____13899 =
                                                   let uu____13918 =
                                                     let uu____13927 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         x in
                                                     [uu____13927] in
                                                   (uu____13918, body1,
                                                     (FStar_Pervasives_Native.Some
                                                        body_rc)) in
                                                 FStar_Syntax_Syntax.Tm_abs
                                                   uu____13899 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13898
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close =
                                               closure_as_term cfg env1 in
                                             let bind_inst =
                                               let uu____13966 =
                                                 let uu____13967 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____13967.FStar_Syntax_Syntax.n in
                                               match uu____13966 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind,
                                                    uu____13973::uu____13974::[])
                                                   ->
                                                   let uu____13979 =
                                                     let uu____13980 =
                                                       let uu____13987 =
                                                         let uu____13988 =
                                                           let uu____13989 =
                                                             close
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.FStar_TypeChecker_Cfg.tcenv
                                                             uu____13989 in
                                                         let uu____13990 =
                                                           let uu____13993 =
                                                             let uu____13994
                                                               = close t in
                                                             (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.FStar_TypeChecker_Cfg.tcenv
                                                               uu____13994 in
                                                           [uu____13993] in
                                                         uu____13988 ::
                                                           uu____13990 in
                                                       (bind, uu____13987) in
                                                     FStar_Syntax_Syntax.Tm_uinst
                                                       uu____13980 in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____13979 rng
                                               | uu____13997 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let bind_inst_args f_arg =
                                               let uu____14008 =
                                                 FStar_Syntax_Util.is_layered
                                                   ed in
                                               if uu____14008
                                               then
                                                 let unit_args =
                                                   let uu____14014 =
                                                     let uu____14015 =
                                                       let uu____14018 =
                                                         let uu____14019 =
                                                           FStar_All.pipe_right
                                                             ed
                                                             FStar_Syntax_Util.get_bind_vc_combinator in
                                                         FStar_All.pipe_right
                                                           uu____14019
                                                           FStar_Pervasives_Native.snd in
                                                       FStar_All.pipe_right
                                                         uu____14018
                                                         FStar_Syntax_Subst.compress in
                                                     uu____14015.FStar_Syntax_Syntax.n in
                                                   match uu____14014 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (uu____14052::uu____14053::bs,
                                                        uu____14055)
                                                       when
                                                       (FStar_List.length bs)
                                                         >=
                                                         (Prims.of_int (2))
                                                       ->
                                                       let uu____14106 =
                                                         let uu____14115 =
                                                           FStar_All.pipe_right
                                                             bs
                                                             (FStar_List.splitAt
                                                                ((FStar_List.length
                                                                    bs)
                                                                   -
                                                                   (Prims.of_int (2)))) in
                                                         FStar_All.pipe_right
                                                           uu____14115
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____14106
                                                         (FStar_List.map
                                                            (fun uu____14237
                                                               ->
                                                               FStar_Syntax_Syntax.as_arg
                                                                 FStar_Syntax_Syntax.unit_const))
                                                   | uu____14244 ->
                                                       let uu____14245 =
                                                         let uu____14250 =
                                                           let uu____14251 =
                                                             FStar_Ident.string_of_lid
                                                               ed.FStar_Syntax_Syntax.mname in
                                                           let uu____14252 =
                                                             let uu____14253
                                                               =
                                                               let uu____14254
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator in
                                                               FStar_All.pipe_right
                                                                 uu____14254
                                                                 FStar_Pervasives_Native.snd in
                                                             FStar_All.pipe_right
                                                               uu____14253
                                                               FStar_Syntax_Print.term_to_string in
                                                           FStar_Util.format2
                                                             "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                             uu____14251
                                                             uu____14252 in
                                                         (FStar_Errors.Fatal_UnexpectedEffect,
                                                           uu____14250) in
                                                       FStar_Errors.raise_error
                                                         uu____14245 rng in
                                                 let uu____14277 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____14278 =
                                                   let uu____14281 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____14282 =
                                                     let uu____14285 =
                                                       let uu____14288 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           f_arg in
                                                       let uu____14289 =
                                                         let uu____14292 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2 in
                                                         [uu____14292] in
                                                       uu____14288 ::
                                                         uu____14289 in
                                                     FStar_List.append
                                                       unit_args uu____14285 in
                                                   uu____14281 :: uu____14282 in
                                                 uu____14277 :: uu____14278
                                               else
                                                 (let maybe_range_arg =
                                                    let uu____14297 =
                                                      FStar_Util.for_some
                                                        (FStar_Syntax_Util.attr_eq
                                                           FStar_Syntax_Util.dm4f_bind_range_attr)
                                                        ed.FStar_Syntax_Syntax.eff_attrs in
                                                    if uu____14297
                                                    then
                                                      let uu____14300 =
                                                        let uu____14301 =
                                                          FStar_TypeChecker_Cfg.embed_simple
                                                            FStar_Syntax_Embeddings.e_range
                                                            lb.FStar_Syntax_Syntax.lbpos
                                                            lb.FStar_Syntax_Syntax.lbpos in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____14301 in
                                                      let uu____14302 =
                                                        let uu____14305 =
                                                          let uu____14306 =
                                                            FStar_TypeChecker_Cfg.embed_simple
                                                              FStar_Syntax_Embeddings.e_range
                                                              body2.FStar_Syntax_Syntax.pos
                                                              body2.FStar_Syntax_Syntax.pos in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu____14306 in
                                                        [uu____14305] in
                                                      uu____14300 ::
                                                        uu____14302
                                                    else [] in
                                                  let uu____14308 =
                                                    let uu____14311 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp in
                                                    let uu____14312 =
                                                      let uu____14315 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t in
                                                      [uu____14315] in
                                                    uu____14311 ::
                                                      uu____14312 in
                                                  let uu____14316 =
                                                    let uu____14319 =
                                                      let uu____14322 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun in
                                                      let uu____14323 =
                                                        let uu____14326 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            f_arg in
                                                        let uu____14327 =
                                                          let uu____14330 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu____14331 =
                                                            let uu____14334 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2 in
                                                            [uu____14334] in
                                                          uu____14330 ::
                                                            uu____14331 in
                                                        uu____14326 ::
                                                          uu____14327 in
                                                      uu____14322 ::
                                                        uu____14323 in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____14319 in
                                                  FStar_List.append
                                                    uu____14308 uu____14316) in
                                             let reified =
                                               let is_total_effect =
                                                 FStar_TypeChecker_Env.is_total_effect
                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                   eff_name in
                                               if is_total_effect
                                               then
                                                 let uu____14337 =
                                                   let uu____14338 =
                                                     let uu____14355 =
                                                       bind_inst_args head in
                                                     (bind_inst, uu____14355) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____14338 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____14337 rng
                                               else
                                                 (let uu____14379 =
                                                    let bv =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        x.FStar_Syntax_Syntax.sort in
                                                    let lb1 =
                                                      let uu____14388 =
                                                        let uu____14391 =
                                                          let uu____14402 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              x.FStar_Syntax_Syntax.sort in
                                                          [uu____14402] in
                                                        FStar_Syntax_Util.mk_app
                                                          repr uu____14391 in
                                                      {
                                                        FStar_Syntax_Syntax.lbname
                                                          =
                                                          (FStar_Util.Inl bv);
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = [];
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____14388;
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
                                                    let uu____14430 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        bv in
                                                    (lb1, bv, uu____14430) in
                                                  match uu____14379 with
                                                  | (lb_head, head_bv, head1)
                                                      ->
                                                      let uu____14434 =
                                                        let uu____14435 =
                                                          let uu____14448 =
                                                            let uu____14451 =
                                                              let uu____14458
                                                                =
                                                                let uu____14459
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    head_bv in
                                                                [uu____14459] in
                                                              FStar_Syntax_Subst.close
                                                                uu____14458 in
                                                            let uu____14478 =
                                                              let uu____14479
                                                                =
                                                                let uu____14480
                                                                  =
                                                                  let uu____14497
                                                                    =
                                                                    bind_inst_args
                                                                    head1 in
                                                                  (bind_inst,
                                                                    uu____14497) in
                                                                FStar_Syntax_Syntax.Tm_app
                                                                  uu____14480 in
                                                              FStar_Syntax_Syntax.mk
                                                                uu____14479
                                                                rng in
                                                            FStar_All.pipe_left
                                                              uu____14451
                                                              uu____14478 in
                                                          ((false, [lb_head]),
                                                            uu____14448) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____14435 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____14434 rng) in
                                             FStar_TypeChecker_Cfg.log cfg
                                               (fun uu____14536 ->
                                                  let uu____14537 =
                                                    FStar_Syntax_Print.term_to_string
                                                      top0 in
                                                  let uu____14538 =
                                                    FStar_Syntax_Print.term_to_string
                                                      reified in
                                                  FStar_Util.print2
                                                    "Reified (1) <%s> to %s\n"
                                                    uu____14537 uu____14538);
                                             (let uu____14539 =
                                                FStar_List.tl stack1 in
                                              norm cfg env1 uu____14539
                                                reified))))))
                  | FStar_Syntax_Syntax.Tm_app (head, args) ->
                      ((let uu____14567 = FStar_Options.defensive () in
                        if uu____14567
                        then
                          let is_arg_impure uu____14579 =
                            match uu____14579 with
                            | (e, q) ->
                                let uu____14592 =
                                  let uu____14593 =
                                    FStar_Syntax_Subst.compress e in
                                  uu____14593.FStar_Syntax_Syntax.n in
                                (match uu____14592 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,
                                      FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1, m2, t'))
                                     ->
                                     let uu____14608 =
                                       FStar_Syntax_Util.is_pure_effect m1 in
                                     Prims.op_Negation uu____14608
                                 | uu____14609 -> false) in
                          let uu____14610 =
                            let uu____14611 =
                              let uu____14622 =
                                FStar_Syntax_Syntax.as_arg head in
                              uu____14622 :: args in
                            FStar_Util.for_some is_arg_impure uu____14611 in
                          (if uu____14610
                           then
                             let uu____14647 =
                               let uu____14652 =
                                 let uu____14653 =
                                   FStar_Syntax_Print.term_to_string top2 in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____14653 in
                               (FStar_Errors.Warning_Defensive, uu____14652) in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____14647
                           else ())
                        else ());
                       (let fallback1 uu____14661 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____14665 ->
                               let uu____14666 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____14666 "");
                          (let uu____14667 = FStar_List.tl stack1 in
                           let uu____14668 = FStar_Syntax_Util.mk_reify top2 in
                           norm cfg env1 uu____14667 uu____14668) in
                        let fallback2 uu____14674 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____14678 ->
                               let uu____14679 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____14679 "");
                          (let uu____14680 = FStar_List.tl stack1 in
                           let uu____14681 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos in
                           norm cfg env1 uu____14680 uu____14681) in
                        let uu____14686 =
                          let uu____14687 = FStar_Syntax_Util.un_uinst head in
                          uu____14687.FStar_Syntax_Syntax.n in
                        match uu____14686 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid in
                            let uu____14693 =
                              let uu____14694 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid in
                              Prims.op_Negation uu____14694 in
                            if uu____14693
                            then fallback1 ()
                            else
                              (let uu____14696 =
                                 let uu____14697 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isNone uu____14697 in
                               if uu____14696
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____14710 =
                                      FStar_Syntax_Util.mk_reify head in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____14710
                                      args t.FStar_Syntax_Syntax.pos in
                                  let uu____14711 = FStar_List.tl stack1 in
                                  norm cfg env1 uu____14711 t1))
                        | uu____14712 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic uu____14714) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, t'))
                      ->
                      let lifted =
                        let uu____14738 = closure_as_term cfg env1 t' in
                        reify_lift cfg e msrc mtgt uu____14738 in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____14742 ->
                            let uu____14743 =
                              FStar_Syntax_Print.term_to_string lifted in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____14743);
                       (let uu____14744 = FStar_List.tl stack1 in
                        norm cfg env1 uu____14744 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e, branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____14865 ->
                                match uu____14865 with
                                | (pat, wopt, tm) ->
                                    let uu____14913 =
                                      FStar_Syntax_Util.mk_reify tm in
                                    (pat, wopt, uu____14913))) in
                      let tm =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos in
                      let uu____14945 = FStar_List.tl stack1 in
                      norm cfg env1 uu____14945 tm
                  | uu____14946 -> fallback ()))
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
              (fun uu____14960 ->
                 let uu____14961 = FStar_Ident.string_of_lid msrc in
                 let uu____14962 = FStar_Ident.string_of_lid mtgt in
                 let uu____14963 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14961
                   uu____14962 uu____14963);
            (let uu____14964 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____14966 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1) in
                  Prims.op_Negation uu____14966) in
             if uu____14964
             then
               let ed =
                 let uu____14968 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____14968 in
               let uu____14969 =
                 let uu____14978 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 FStar_All.pipe_right uu____14978 FStar_Util.must in
               match uu____14969 with
               | (uu____15025, repr) ->
                   let uu____15035 =
                     let uu____15044 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr in
                     FStar_All.pipe_right uu____15044 FStar_Util.must in
                   (match uu____15035 with
                    | (uu____15091, return_repr) ->
                        let return_inst =
                          let uu____15104 =
                            let uu____15105 =
                              FStar_Syntax_Subst.compress return_repr in
                            uu____15105.FStar_Syntax_Syntax.n in
                          match uu____15104 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm, uu____15111::[]) ->
                              let uu____15116 =
                                let uu____15117 =
                                  let uu____15124 =
                                    let uu____15125 =
                                      env1.FStar_TypeChecker_Env.universe_of
                                        env1 t in
                                    [uu____15125] in
                                  (return_tm, uu____15124) in
                                FStar_Syntax_Syntax.Tm_uinst uu____15117 in
                              FStar_Syntax_Syntax.mk uu____15116
                                e.FStar_Syntax_Syntax.pos
                          | uu____15128 ->
                              failwith "NIY : Reification of indexed effects" in
                        let uu____15131 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t in
                          let lb =
                            let uu____15142 =
                              let uu____15145 =
                                let uu____15156 =
                                  FStar_Syntax_Syntax.as_arg t in
                                [uu____15156] in
                              FStar_Syntax_Util.mk_app repr uu____15145 in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____15142;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            } in
                          let uu____15183 = FStar_Syntax_Syntax.bv_to_name bv in
                          (lb, bv, uu____15183) in
                        (match uu____15131 with
                         | (lb_e, e_bv, e1) ->
                             let uu____15195 =
                               let uu____15196 =
                                 let uu____15209 =
                                   let uu____15212 =
                                     let uu____15219 =
                                       let uu____15220 =
                                         FStar_Syntax_Syntax.mk_binder e_bv in
                                       [uu____15220] in
                                     FStar_Syntax_Subst.close uu____15219 in
                                   let uu____15239 =
                                     let uu____15240 =
                                       let uu____15241 =
                                         let uu____15258 =
                                           let uu____15269 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____15278 =
                                             let uu____15289 =
                                               FStar_Syntax_Syntax.as_arg e1 in
                                             [uu____15289] in
                                           uu____15269 :: uu____15278 in
                                         (return_inst, uu____15258) in
                                       FStar_Syntax_Syntax.Tm_app uu____15241 in
                                     FStar_Syntax_Syntax.mk uu____15240
                                       e1.FStar_Syntax_Syntax.pos in
                                   FStar_All.pipe_left uu____15212
                                     uu____15239 in
                                 ((false, [lb_e]), uu____15209) in
                               FStar_Syntax_Syntax.Tm_let uu____15196 in
                             FStar_Syntax_Syntax.mk uu____15195
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____15347 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt in
                match uu____15347 with
                | FStar_Pervasives_Native.None ->
                    let uu____15350 =
                      let uu____15351 = FStar_Ident.string_of_lid msrc in
                      let uu____15352 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15351 uu____15352 in
                    failwith uu____15350
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15353;
                      FStar_TypeChecker_Env.mtarget = uu____15354;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15355;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None;_};_}
                    ->
                    let uu____15375 =
                      let uu____15376 = FStar_Ident.string_of_lid msrc in
                      let uu____15377 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15376 uu____15377 in
                    failwith uu____15375
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15378;
                      FStar_TypeChecker_Env.mtarget = uu____15379;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15380;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____15411 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc in
                      if uu____15411
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____15413 =
                           let uu____15414 =
                             let uu____15433 =
                               let uu____15442 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_Syntax_Syntax.t_unit in
                               [uu____15442] in
                             (uu____15433, e,
                               (FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      msrc;
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t);
                                    FStar_Syntax_Syntax.residual_flags = []
                                  })) in
                           FStar_Syntax_Syntax.Tm_abs uu____15414 in
                         FStar_Syntax_Syntax.mk uu____15413
                           e.FStar_Syntax_Syntax.pos) in
                    let uu____15475 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t in
                    lift uu____15475 t e1))
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
                (fun uu____15545 ->
                   match uu____15545 with
                   | (a, imp) ->
                       let uu____15564 = norm cfg env1 [] a in
                       (uu____15564, imp))))
and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg ->
    fun env1 ->
      fun comp ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____15574 ->
             let uu____15575 = FStar_Syntax_Print.comp_to_string comp in
             let uu____15576 =
               FStar_Util.string_of_int (FStar_List.length env1) in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____15575 uu____15576);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15600 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____15603 ->
                        FStar_Pervasives_Native.Some uu____15603) uu____15600
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2128_15604 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2128_15604.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2128_15604.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15626 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____15629 ->
                        FStar_Pervasives_Native.Some uu____15629) uu____15626
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2139_15630 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2139_15630.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2139_15630.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx ->
                    fun uu____15675 ->
                      match uu____15675 with
                      | (a, i) ->
                          let uu____15694 = norm cfg env1 [] a in
                          (uu____15694, i)) in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_15716 ->
                       match uu___14_15716 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15720 = norm cfg env1 [] t in
                           FStar_Syntax_Syntax.DECREASES uu____15720
                       | f -> f)) in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ in
             let uu___2156_15728 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2158_15731 = ct in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2158_15731.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2156_15728.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2156_15728.FStar_Syntax_Syntax.vars)
             })
and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg ->
    fun env1 ->
      fun b ->
        let uu____15735 = b in
        match uu____15735 with
        | (x, imp) ->
            let x1 =
              let uu___2166_15743 = x in
              let uu____15744 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2166_15743.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2166_15743.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15744
              } in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
                  let uu____15755 =
                    let uu____15756 =
                      let uu____15757 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____15757 in
                    FStar_Syntax_Syntax.Meta uu____15756 in
                  FStar_Pervasives_Native.Some uu____15755
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
                  let uu____15763 =
                    let uu____15764 =
                      let uu____15765 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____15765 in
                    FStar_Syntax_Syntax.Meta uu____15764 in
                  FStar_Pervasives_Native.Some uu____15763
              | i -> i in
            (x1, imp1)
and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu____15776 =
          FStar_List.fold_left
            (fun uu____15810 ->
               fun b ->
                 match uu____15810 with
                 | (nbs', env2) ->
                     let b1 = norm_binder cfg env2 b in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs in
        match uu____15776 with | (nbs, uu____15890) -> FStar_List.rev nbs
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
            let uu____15922 =
              let uu___2196_15923 = rc in
              let uu____15924 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2196_15923.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15924;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2196_15923.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____15922
        | uu____15940 -> lopt
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
            (let uu____15949 = FStar_Syntax_Print.term_to_string tm in
             let uu____15950 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____15949 uu____15950)
          else ();
          tm'
and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg ->
    fun uu___15_15954 ->
      match uu___15_15954 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____15967 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l in
          (match uu____15967 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None ->
               let uu____15971 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None in
               FStar_Syntax_Syntax.fv_to_tm uu____15971)
and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let tm1 =
            let uu____15979 = norm_cb cfg in
            reduce_primops uu____15979 cfg env1 tm in
          let uu____15984 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify in
          if uu____15984
          then tm1
          else
            (let w t =
               let uu___2225_15998 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2225_15998.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2225_15998.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               let uu____16009 =
                 let uu____16010 = FStar_Syntax_Util.unmeta t in
                 uu____16010.FStar_Syntax_Syntax.n in
               match uu____16009 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16017 -> FStar_Pervasives_Native.None in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t, uu____16078)::args1, (bv, uu____16081)::bs1) ->
                   let uu____16135 =
                     let uu____16136 = FStar_Syntax_Subst.compress t in
                     uu____16136.FStar_Syntax_Syntax.n in
                   (match uu____16135 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16140 -> false)
               | ([], []) -> true
               | (uu____16169, uu____16170) -> false in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16219 = FStar_Syntax_Print.term_to_string t in
                  let uu____16220 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16219
                    uu____16220)
               else ();
               (let uu____16222 = FStar_Syntax_Util.head_and_args' t in
                match uu____16222 with
                | (hd, args) ->
                    let uu____16261 =
                      let uu____16262 = FStar_Syntax_Subst.compress hd in
                      uu____16262.FStar_Syntax_Syntax.n in
                    (match uu____16261 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____16269 =
                               FStar_Syntax_Print.term_to_string t in
                             let uu____16270 =
                               FStar_Syntax_Print.bv_to_string bv in
                             let uu____16271 =
                               FStar_Syntax_Print.term_to_string hd in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____16269 uu____16270 uu____16271)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____16273 -> FStar_Pervasives_Native.None)) in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16290 = FStar_Syntax_Print.term_to_string t in
                  let uu____16291 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____16290
                    uu____16291)
               else ();
               (let uu____16293 = FStar_Syntax_Util.is_squash t in
                match uu____16293 with
                | FStar_Pervasives_Native.Some (uu____16304, t') ->
                    is_applied bs t'
                | uu____16316 ->
                    let uu____16325 = FStar_Syntax_Util.is_auto_squash t in
                    (match uu____16325 with
                     | FStar_Pervasives_Native.Some (uu____16336, t') ->
                         is_applied bs t'
                     | uu____16348 -> is_applied bs t)) in
             let is_quantified_const bv phi =
               let uu____16372 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____16372 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid, (p, uu____16379)::(q, uu____16381)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16423 = FStar_Syntax_Print.term_to_string p in
                       let uu____16424 = FStar_Syntax_Print.term_to_string q in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____16423 uu____16424)
                    else ();
                    (let uu____16426 =
                       FStar_Syntax_Util.destruct_typ_as_formula p in
                     match uu____16426 with
                     | FStar_Pervasives_Native.None ->
                         let uu____16431 =
                           let uu____16432 = FStar_Syntax_Subst.compress p in
                           uu____16432.FStar_Syntax_Syntax.n in
                         (match uu____16431 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____16440 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q in
                                FStar_Pervasives_Native.Some uu____16440))
                          | uu____16443 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1, (p1, uu____16446)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____16471 =
                           let uu____16472 = FStar_Syntax_Subst.compress p1 in
                           uu____16472.FStar_Syntax_Syntax.n in
                         (match uu____16471 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____16480 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q in
                                FStar_Pervasives_Native.Some uu____16480))
                          | uu____16483 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs, pats, phi1)) ->
                         let uu____16487 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1 in
                         (match uu____16487 with
                          | FStar_Pervasives_Native.None ->
                              let uu____16492 =
                                is_applied_maybe_squashed bs phi1 in
                              (match uu____16492 with
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
                                     let uu____16503 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____16503))
                               | uu____16506 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1, (p1, uu____16511)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____16536 =
                                is_applied_maybe_squashed bs p1 in
                              (match uu____16536 with
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
                                     let uu____16547 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____16547))
                               | uu____16550 -> FStar_Pervasives_Native.None)
                          | uu____16553 -> FStar_Pervasives_Native.None)
                     | uu____16556 -> FStar_Pervasives_Native.None))
               | uu____16559 -> FStar_Pervasives_Native.None in
             let is_forall_const phi =
               let uu____16572 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____16572 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv, uu____16578)::[], uu____16579, phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16598 = FStar_Syntax_Print.bv_to_string bv in
                       let uu____16599 =
                         FStar_Syntax_Print.term_to_string phi' in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____16598
                         uu____16599)
                    else ();
                    is_quantified_const bv phi')
               | uu____16601 -> FStar_Pervasives_Native.None in
             let is_const_match phi =
               let uu____16614 =
                 let uu____16615 = FStar_Syntax_Subst.compress phi in
                 uu____16615.FStar_Syntax_Syntax.n in
               match uu____16614 with
               | FStar_Syntax_Syntax.Tm_match (uu____16620, br::brs) ->
                   let uu____16687 = br in
                   (match uu____16687 with
                    | (uu____16704, uu____16705, e) ->
                        let r =
                          let uu____16726 = simp_t e in
                          match uu____16726 with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16732 =
                                FStar_List.for_all
                                  (fun uu____16750 ->
                                     match uu____16750 with
                                     | (uu____16763, uu____16764, e') ->
                                         let uu____16778 = simp_t e' in
                                         uu____16778 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs in
                              if uu____16732
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None in
                        r)
               | uu____16786 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____16795 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____16795
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16828 =
                 match uu____16828 with
                 | (t1, q) ->
                     let uu____16849 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____16849 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
                      | uu____16881 -> (t1, q)) in
               let uu____16894 = FStar_Syntax_Util.head_and_args t in
               match uu____16894 with
               | (head, args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     t.FStar_Syntax_Syntax.pos in
             let rec clearly_inhabited ty =
               let uu____16970 =
                 let uu____16971 = FStar_Syntax_Util.unmeta ty in
                 uu____16971.FStar_Syntax_Syntax.n in
               match uu____16970 with
               | FStar_Syntax_Syntax.Tm_uinst (t, uu____16975) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16980, c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17004 -> false in
             let simplify arg =
               let uu____17035 = simp_t (FStar_Pervasives_Native.fst arg) in
               (uu____17035, arg) in
             let uu____17048 = is_forall_const tm1 in
             match uu____17048 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____17053 = FStar_Syntax_Print.term_to_string tm1 in
                     let uu____17054 = FStar_Syntax_Print.term_to_string tm' in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____17053
                       uu____17054)
                  else ();
                  (let uu____17056 = norm cfg env1 [] tm' in
                   maybe_simplify_aux cfg env1 stack1 uu____17056))
             | FStar_Pervasives_Native.None ->
                 let uu____17057 =
                   let uu____17058 = FStar_Syntax_Subst.compress tm1 in
                   uu____17058.FStar_Syntax_Syntax.n in
                 (match uu____17057 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17062;
                              FStar_Syntax_Syntax.vars = uu____17063;_},
                            uu____17064);
                         FStar_Syntax_Syntax.pos = uu____17065;
                         FStar_Syntax_Syntax.vars = uu____17066;_},
                       args)
                      ->
                      let uu____17096 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____17096
                      then
                        let uu____17097 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____17097 with
                         | (FStar_Pervasives_Native.Some (true), uu____17152)::
                             (uu____17153, (arg, uu____17155))::[] ->
                             maybe_auto_squash arg
                         | (uu____17220, (arg, uu____17222))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____17223)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____17288)::uu____17289::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17352::(FStar_Pervasives_Native.Some
                                         (false), uu____17353)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17416 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17432 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____17432
                         then
                           let uu____17433 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____17433 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____17488)::uu____17489::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17552::(FStar_Pervasives_Native.Some
                                           (true), uu____17553)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____17616)::(uu____17617, (arg, uu____17619))::[]
                               -> maybe_auto_squash arg
                           | (uu____17684, (arg, uu____17686))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____17687)::[]
                               -> maybe_auto_squash arg
                           | uu____17752 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17768 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____17768
                            then
                              let uu____17769 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____17769 with
                              | uu____17824::(FStar_Pervasives_Native.Some
                                              (true), uu____17825)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____17888)::uu____17889::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____17952)::(uu____17953,
                                                (arg, uu____17955))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18020, (p, uu____18022))::(uu____18023,
                                                                  (q,
                                                                   uu____18025))::[]
                                  ->
                                  let uu____18090 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____18090
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18092 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18108 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____18108
                               then
                                 let uu____18109 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____18109 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18164)::(FStar_Pervasives_Native.Some
                                                   (true), uu____18165)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18230)::(FStar_Pervasives_Native.Some
                                                   (false), uu____18231)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18296)::(FStar_Pervasives_Native.Some
                                                   (false), uu____18297)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18362)::(FStar_Pervasives_Native.Some
                                                   (true), uu____18363)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18428, (arg, uu____18430))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____18431)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____18496)::(uu____18497,
                                                   (arg, uu____18499))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18564, (arg, uu____18566))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____18567)::[]
                                     ->
                                     let uu____18632 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____18632
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____18633)::(uu____18634,
                                                   (arg, uu____18636))::[]
                                     ->
                                     let uu____18701 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____18701
                                 | (uu____18702, (p, uu____18704))::(uu____18705,
                                                                    (q,
                                                                    uu____18707))::[]
                                     ->
                                     let uu____18772 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____18772
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18774 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18790 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____18790
                                  then
                                    let uu____18791 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____18791 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____18846)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____18885)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18924 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18940 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____18940
                                     then
                                       match args with
                                       | (t, uu____18942)::[] ->
                                           let uu____18967 =
                                             let uu____18968 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____18968.FStar_Syntax_Syntax.n in
                                           (match uu____18967 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18971::[], body,
                                                 uu____18973)
                                                ->
                                                let uu____19008 = simp_t body in
                                                (match uu____19008 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19011 -> tm1)
                                            | uu____19014 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19016))::(t, uu____19018)::[]
                                           ->
                                           let uu____19057 =
                                             let uu____19058 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____19058.FStar_Syntax_Syntax.n in
                                           (match uu____19057 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19061::[], body,
                                                 uu____19063)
                                                ->
                                                let uu____19098 = simp_t body in
                                                (match uu____19098 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19101 -> tm1)
                                            | uu____19104 -> tm1)
                                       | uu____19105 -> tm1
                                     else
                                       (let uu____19117 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____19117
                                        then
                                          match args with
                                          | (t, uu____19119)::[] ->
                                              let uu____19144 =
                                                let uu____19145 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____19145.FStar_Syntax_Syntax.n in
                                              (match uu____19144 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19148::[], body,
                                                    uu____19150)
                                                   ->
                                                   let uu____19185 =
                                                     simp_t body in
                                                   (match uu____19185 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19188 -> tm1)
                                               | uu____19191 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19193))::(t, uu____19195)::[]
                                              ->
                                              let uu____19234 =
                                                let uu____19235 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____19235.FStar_Syntax_Syntax.n in
                                              (match uu____19234 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19238::[], body,
                                                    uu____19240)
                                                   ->
                                                   let uu____19275 =
                                                     simp_t body in
                                                   (match uu____19275 with
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
                                                    | uu____19278 -> tm1)
                                               | uu____19281 -> tm1)
                                          | uu____19282 -> tm1
                                        else
                                          (let uu____19294 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____19294
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19295;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19296;_},
                                                uu____19297)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19322;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19323;_},
                                                uu____19324)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19349 -> tm1
                                           else
                                             (let uu____19361 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____19361
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____19371 =
                                                    let uu____19372 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____19372.FStar_Syntax_Syntax.n in
                                                  match uu____19371 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____19380 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____19390 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____19390
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____19429 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____19429
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____19431 =
                                                         let uu____19432 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____19432.FStar_Syntax_Syntax.n in
                                                       match uu____19431 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____19435 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____19443 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____19443
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____19448
                                                                  =
                                                                  let uu____19449
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____19449.FStar_Syntax_Syntax.n in
                                                                match uu____19448
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____19455)
                                                                    -> hd
                                                                | uu____19480
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____19483
                                                                =
                                                                let uu____19494
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____19494] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____19483)
                                                       | uu____19527 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____19530 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____19530 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____19550 ->
                                                     let uu____19559 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____19559 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____19565;
                         FStar_Syntax_Syntax.vars = uu____19566;_},
                       args)
                      ->
                      let uu____19592 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____19592
                      then
                        let uu____19593 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____19593 with
                         | (FStar_Pervasives_Native.Some (true), uu____19648)::
                             (uu____19649, (arg, uu____19651))::[] ->
                             maybe_auto_squash arg
                         | (uu____19716, (arg, uu____19718))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____19719)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____19784)::uu____19785::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19848::(FStar_Pervasives_Native.Some
                                         (false), uu____19849)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19912 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19928 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____19928
                         then
                           let uu____19929 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____19929 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____19984)::uu____19985::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20048::(FStar_Pervasives_Native.Some
                                           (true), uu____20049)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____20112)::(uu____20113, (arg, uu____20115))::[]
                               -> maybe_auto_squash arg
                           | (uu____20180, (arg, uu____20182))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____20183)::[]
                               -> maybe_auto_squash arg
                           | uu____20248 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20264 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____20264
                            then
                              let uu____20265 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____20265 with
                              | uu____20320::(FStar_Pervasives_Native.Some
                                              (true), uu____20321)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____20384)::uu____20385::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____20448)::(uu____20449,
                                                (arg, uu____20451))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20516, (p, uu____20518))::(uu____20519,
                                                                  (q,
                                                                   uu____20521))::[]
                                  ->
                                  let uu____20586 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____20586
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20588 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20604 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____20604
                               then
                                 let uu____20605 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____20605 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20660)::(FStar_Pervasives_Native.Some
                                                   (true), uu____20661)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20726)::(FStar_Pervasives_Native.Some
                                                   (false), uu____20727)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20792)::(FStar_Pervasives_Native.Some
                                                   (false), uu____20793)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20858)::(FStar_Pervasives_Native.Some
                                                   (true), uu____20859)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20924, (arg, uu____20926))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____20927)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20992)::(uu____20993,
                                                   (arg, uu____20995))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21060, (arg, uu____21062))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____21063)::[]
                                     ->
                                     let uu____21128 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____21128
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____21129)::(uu____21130,
                                                   (arg, uu____21132))::[]
                                     ->
                                     let uu____21197 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____21197
                                 | (uu____21198, (p, uu____21200))::(uu____21201,
                                                                    (q,
                                                                    uu____21203))::[]
                                     ->
                                     let uu____21268 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____21268
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21270 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21286 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____21286
                                  then
                                    let uu____21287 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____21287 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____21342)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____21381)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21420 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21436 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____21436
                                     then
                                       match args with
                                       | (t, uu____21438)::[] ->
                                           let uu____21463 =
                                             let uu____21464 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____21464.FStar_Syntax_Syntax.n in
                                           (match uu____21463 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21467::[], body,
                                                 uu____21469)
                                                ->
                                                let uu____21504 = simp_t body in
                                                (match uu____21504 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21507 -> tm1)
                                            | uu____21510 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21512))::(t, uu____21514)::[]
                                           ->
                                           let uu____21553 =
                                             let uu____21554 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____21554.FStar_Syntax_Syntax.n in
                                           (match uu____21553 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21557::[], body,
                                                 uu____21559)
                                                ->
                                                let uu____21594 = simp_t body in
                                                (match uu____21594 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21597 -> tm1)
                                            | uu____21600 -> tm1)
                                       | uu____21601 -> tm1
                                     else
                                       (let uu____21613 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____21613
                                        then
                                          match args with
                                          | (t, uu____21615)::[] ->
                                              let uu____21640 =
                                                let uu____21641 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____21641.FStar_Syntax_Syntax.n in
                                              (match uu____21640 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21644::[], body,
                                                    uu____21646)
                                                   ->
                                                   let uu____21681 =
                                                     simp_t body in
                                                   (match uu____21681 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21684 -> tm1)
                                               | uu____21687 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21689))::(t, uu____21691)::[]
                                              ->
                                              let uu____21730 =
                                                let uu____21731 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____21731.FStar_Syntax_Syntax.n in
                                              (match uu____21730 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21734::[], body,
                                                    uu____21736)
                                                   ->
                                                   let uu____21771 =
                                                     simp_t body in
                                                   (match uu____21771 with
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
                                                    | uu____21774 -> tm1)
                                               | uu____21777 -> tm1)
                                          | uu____21778 -> tm1
                                        else
                                          (let uu____21790 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____21790
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21791;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21792;_},
                                                uu____21793)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21818;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21819;_},
                                                uu____21820)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21845 -> tm1
                                           else
                                             (let uu____21857 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____21857
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____21867 =
                                                    let uu____21868 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____21868.FStar_Syntax_Syntax.n in
                                                  match uu____21867 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21876 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21886 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____21886
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____21921 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____21921
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21923 =
                                                         let uu____21924 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____21924.FStar_Syntax_Syntax.n in
                                                       match uu____21923 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21927 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____21935 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____21935
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21940
                                                                  =
                                                                  let uu____21941
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____21941.FStar_Syntax_Syntax.n in
                                                                match uu____21940
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____21947)
                                                                    -> hd
                                                                | uu____21972
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____21975
                                                                =
                                                                let uu____21986
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____21986] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21975)
                                                       | uu____22019 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22022 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____22022 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22042 ->
                                                     let uu____22051 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____22051 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
                      let uu____22062 = simp_t t in
                      (match uu____22062 with
                       | FStar_Pervasives_Native.Some (true) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false) -> tm1
                       | FStar_Pervasives_Native.None -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22065 ->
                      let uu____22088 = is_const_match tm1 in
                      (match uu____22088 with
                       | FStar_Pervasives_Native.Some (true) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None -> tm1)
                  | uu____22091 -> tm1))
and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____22101 ->
               (let uu____22103 = FStar_Syntax_Print.tag_of_term t in
                let uu____22104 = FStar_Syntax_Print.term_to_string t in
                let uu____22105 =
                  FStar_Util.string_of_int (FStar_List.length env1) in
                let uu____22112 =
                  let uu____22113 =
                    let uu____22116 = firstn (Prims.of_int (4)) stack1 in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22116 in
                  stack_to_string uu____22113 in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22103 uu____22104 uu____22105 uu____22112);
               (let uu____22139 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild") in
                if uu____22139
                then
                  let uu____22140 = FStar_Syntax_Util.unbound_variables t in
                  match uu____22140 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22147 = FStar_Syntax_Print.tag_of_term t in
                        let uu____22148 = FStar_Syntax_Print.term_to_string t in
                        let uu____22149 =
                          let uu____22150 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string) in
                          FStar_All.pipe_right uu____22150
                            (FStar_String.concat ", ") in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22147
                          uu____22148 uu____22149);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t in
           let uu____22163 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____22168)::uu____22169 -> true
                | uu____22178 -> false) in
           if uu____22163
           then
             let uu____22179 = FStar_All.pipe_right f_opt FStar_Util.must in
             FStar_All.pipe_right uu____22179 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t in
              match stack1 with
              | [] -> t1
              | (Debug (tm, time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now () in
                      let uu____22191 =
                        let uu____22192 =
                          let uu____22193 =
                            FStar_Util.time_diff time_then time_now in
                          FStar_Pervasives_Native.snd uu____22193 in
                        FStar_Util.string_of_int uu____22192 in
                      let uu____22198 = FStar_Syntax_Print.term_to_string tm in
                      let uu____22199 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg in
                      let uu____22200 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____22191 uu____22198 uu____22199 uu____22200)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____22206, m, r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____22235 ->
                        let uu____22236 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1 "\tSet memo %s\n" uu____22236);
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
                  let uu____22274 =
                    let uu___2854_22275 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2854_22275.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2854_22275.FStar_Syntax_Syntax.vars)
                    } in
                  rebuild cfg env1 stack2 uu____22274
              | (Arg
                  (Univ uu____22278, uu____22279, uu____22280))::uu____22281
                  -> failwith "Impossible"
              | (Arg (Dummy, uu____22284, uu____22285))::uu____22286 ->
                  failwith "Impossible"
              | (UnivArgs (us, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg, tm, uu____22301, uu____22302), aq, r))::stack2
                  when
                  let uu____22352 = head_of t1 in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22352 ->
                  let t2 =
                    let uu____22354 =
                      let uu____22355 = closure_as_term cfg env_arg tm in
                      (uu____22355, aq) in
                    FStar_Syntax_Syntax.extend_app t1 uu____22354 r in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg, tm, m, uu____22365), aq, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____22418 ->
                        let uu____22419 =
                          FStar_Syntax_Print.term_to_string tm in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____22419);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (let uu____22420 =
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          &&
                          (let uu____22422 = is_partial_primop_app cfg t1 in
                           Prims.op_Negation uu____22422) in
                      if uu____22420
                      then
                        let arg = closure_as_term cfg env_arg tm in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2 in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu____22434 = FStar_ST.op_Bang m in
                      match uu____22434 with
                      | FStar_Pervasives_Native.None ->
                          let uu____22495 =
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                              &&
                              (let uu____22497 = is_partial_primop_app cfg t1 in
                               Prims.op_Negation uu____22497) in
                          if uu____22495
                          then
                            let arg = closure_as_term cfg env_arg tm in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                            rebuild cfg env_arg stack2 t2
                          else
                            (let stack3 = (MemoLazy m) ::
                               (App (env1, t1, aq, r)) :: stack2 in
                             norm cfg env_arg stack3 tm)
                      | FStar_Pervasives_Native.Some (uu____22508, a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq) r in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2, head, aq, r))::stack' when
                  should_reify cfg stack1 ->
                  let t0 = t1 in
                  let fallback msg uu____22561 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____22565 ->
                         let uu____22566 =
                           FStar_Syntax_Print.term_to_string t1 in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____22566);
                    (let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                     rebuild cfg env2 stack' t2) in
                  let is_layered_effect m =
                    let uu____22578 =
                      FStar_All.pipe_right m
                        (FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv) in
                    FStar_All.pipe_right uu____22578
                      (FStar_TypeChecker_Env.is_layered_effect
                         cfg.FStar_TypeChecker_Cfg.tcenv) in
                  let uu____22579 =
                    let uu____22580 = FStar_Syntax_Subst.compress t1 in
                    uu____22580.FStar_Syntax_Syntax.n in
                  (match uu____22579 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____22583, FStar_Syntax_Syntax.Meta_monadic
                        (m, uu____22585))
                       when
                       (FStar_All.pipe_right m is_layered_effect) &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu____22594 =
                         let uu____22595 = FStar_Ident.string_of_lid m in
                         FStar_Util.format1
                           "Meta_monadic for a layered effect %s in non-extraction mode"
                           uu____22595 in
                       fallback uu____22594 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____22596, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, uu____22599))
                       when
                       ((is_layered_effect msrc) || (is_layered_effect mtgt))
                         &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu____22608 =
                         let uu____22609 = FStar_Ident.string_of_lid msrc in
                         let uu____22610 = FStar_Ident.string_of_lid mtgt in
                         FStar_Util.format2
                           "Meta_monadic_lift for layered effect %s ~> %s in non extraction mode"
                           uu____22609 uu____22610 in
                       fallback uu____22608 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, ty))
                       ->
                       let lifted =
                         let uu____22635 = closure_as_term cfg env2 ty in
                         reify_lift cfg t2 msrc mtgt uu____22635 in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____22639 ->
                             let uu____22640 =
                               FStar_Syntax_Print.term_to_string lifted in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____22640);
                        (let uu____22641 = FStar_List.tl stack1 in
                         norm cfg env2 uu____22641 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____22642);
                          FStar_Syntax_Syntax.pos = uu____22643;
                          FStar_Syntax_Syntax.vars = uu____22644;_},
                        (e, uu____22646)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____22685 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____22702 = FStar_Syntax_Util.head_and_args t1 in
                       (match uu____22702 with
                        | (hd, args) ->
                            let uu____22745 =
                              let uu____22746 = FStar_Syntax_Util.un_uinst hd in
                              uu____22746.FStar_Syntax_Syntax.n in
                            (match uu____22745 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____22750 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv in
                                 (match uu____22750 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____22753;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____22754;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____22755;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____22757;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____22758;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____22759;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____22760;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____22789 -> fallback " (3)" ())
                             | uu____22792 -> fallback " (4)" ()))
                   | uu____22793 -> fallback " (2)" ())
              | (App (env2, head, aq, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env', head, aq, r))::stack2 ->
                  let uu____22813 =
                    let uu____22814 =
                      let uu____22815 =
                        let uu____22822 =
                          let uu____22823 =
                            let uu____22854 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            (env1, t1, uu____22854, false) in
                          Clos uu____22823 in
                        (uu____22822, aq, (t1.FStar_Syntax_Syntax.pos)) in
                      Arg uu____22815 in
                    uu____22814 :: stack2 in
                  norm cfg env' uu____22813 head
              | (Match (env', branches1, cfg1, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____22927 ->
                        let uu____22928 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____22928);
                   (let scrutinee_env = env1 in
                    let env2 = env' in
                    let scrutinee = t1 in
                    let norm_and_rebuild_match uu____22937 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____22942 ->
                           let uu____22943 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           let uu____22944 =
                             let uu____22945 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____22972 ->
                                       match uu____22972 with
                                       | (p, uu____22982, uu____22983) ->
                                           FStar_Syntax_Print.pat_to_string p)) in
                             FStar_All.pipe_right uu____22945
                               (FStar_String.concat "\n\t") in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____22943 uu____22944);
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
                                   (fun uu___16_23001 ->
                                      match uu___16_23001 with
                                      | FStar_TypeChecker_Env.InliningDelta
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                          -> true
                                      | uu____23002 -> false)) in
                            let steps =
                              let uu___3048_23004 =
                                cfg1.FStar_TypeChecker_Cfg.steps in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3048_23004.FStar_TypeChecker_Cfg.for_extraction)
                              } in
                            let uu___3051_23009 = cfg1 in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3051_23009.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3051_23009.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3051_23009.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3051_23009.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3051_23009.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3051_23009.FStar_TypeChecker_Cfg.reifying)
                            }) in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2 in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____23081 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                             let uu____23110 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____23194 ->
                                       fun uu____23195 ->
                                         match (uu____23194, uu____23195)
                                         with
                                         | ((pats1, env4), (p1, b)) ->
                                             let uu____23334 =
                                               norm_pat env4 p1 in
                                             (match uu____23334 with
                                              | (p2, env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3)) in
                             (match uu____23110 with
                              | (pats1, env4) ->
                                  ((let uu___3079_23496 = p in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3079_23496.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3083_23515 = x in
                               let uu____23516 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3083_23515.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3083_23515.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____23516
                               } in
                             ((let uu___3086_23530 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3086_23530.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3090_23541 = x in
                               let uu____23542 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3090_23541.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3090_23541.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____23542
                               } in
                             ((let uu___3093_23556 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3093_23556.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                             let x1 =
                               let uu___3099_23572 = x in
                               let uu____23573 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3099_23572.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3099_23572.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____23573
                               } in
                             let t3 = norm_or_whnf env3 t2 in
                             ((let uu___3103_23588 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3103_23588.FStar_Syntax_Syntax.p)
                               }), env3) in
                       let norm_branches uu____23608 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____23625 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch ->
                                     let uu____23641 =
                                       FStar_Syntax_Subst.open_branch branch in
                                     match uu____23641 with
                                     | (p, wopt, e) ->
                                         let uu____23661 = norm_pat env2 p in
                                         (match uu____23661 with
                                          | (p1, env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____23716 =
                                                      norm_or_whnf env3 w in
                                                    FStar_Pervasives_Native.Some
                                                      uu____23716 in
                                              let e1 = norm_or_whnf env3 e in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1)))) in
                       let maybe_commute_matches uu____23735 =
                         let can_commute =
                           match branches1 with
                           | ({
                                FStar_Syntax_Syntax.v =
                                  FStar_Syntax_Syntax.Pat_cons
                                  (fv, uu____23738);
                                FStar_Syntax_Syntax.p = uu____23739;_},
                              uu____23740, uu____23741)::uu____23742 ->
                               FStar_TypeChecker_Env.fv_has_attr
                                 cfg1.FStar_TypeChecker_Cfg.tcenv fv
                                 FStar_Parser_Const.commute_nested_matches_lid
                           | uu____23781 -> false in
                         let uu____23782 =
                           let uu____23783 =
                             FStar_Syntax_Util.unascribe scrutinee in
                           uu____23783.FStar_Syntax_Syntax.n in
                         match uu____23782 with
                         | FStar_Syntax_Syntax.Tm_match (sc0, branches0) when
                             can_commute ->
                             let reduce_branch b =
                               let stack3 =
                                 [Match (env', branches1, cfg1, r)] in
                               let uu____23833 =
                                 FStar_Syntax_Subst.open_branch b in
                               match uu____23833 with
                               | (p, wopt, e) ->
                                   let uu____23853 = norm_pat scrutinee_env p in
                                   (match uu____23853 with
                                    | (p1, branch_env) ->
                                        let wopt1 =
                                          match wopt with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____23908 =
                                                norm_or_whnf branch_env w in
                                              FStar_Pervasives_Native.Some
                                                uu____23908 in
                                        let e1 =
                                          norm cfg1 branch_env stack3 e in
                                        FStar_Syntax_Util.branch
                                          (p1, wopt1, e1)) in
                             let branches01 =
                               FStar_List.map reduce_branch branches0 in
                             let uu____23967 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (sc0, branches01)) r in
                             rebuild cfg1 env2 stack2 uu____23967
                         | uu____23986 ->
                             let scrutinee1 =
                               let uu____23990 =
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
                               if uu____23990
                               then
                                 norm
                                   (let uu___3159_23995 = cfg1 in
                                    {
                                      FStar_TypeChecker_Cfg.steps =
                                        (let uu___3161_23998 =
                                           cfg1.FStar_TypeChecker_Cfg.steps in
                                         {
                                           FStar_TypeChecker_Cfg.beta =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.beta);
                                           FStar_TypeChecker_Cfg.iota =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.iota);
                                           FStar_TypeChecker_Cfg.zeta =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.zeta);
                                           FStar_TypeChecker_Cfg.zeta_full =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.zeta_full);
                                           FStar_TypeChecker_Cfg.weak =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.weak);
                                           FStar_TypeChecker_Cfg.hnf =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.hnf);
                                           FStar_TypeChecker_Cfg.primops =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.primops);
                                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                           FStar_TypeChecker_Cfg.unfold_until
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.unfold_until);
                                           FStar_TypeChecker_Cfg.unfold_only
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.unfold_only);
                                           FStar_TypeChecker_Cfg.unfold_fully
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.unfold_fully);
                                           FStar_TypeChecker_Cfg.unfold_attr
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.unfold_attr);
                                           FStar_TypeChecker_Cfg.unfold_tac =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.unfold_tac);
                                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                           FStar_TypeChecker_Cfg.simplify =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.simplify);
                                           FStar_TypeChecker_Cfg.erase_universes
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.erase_universes);
                                           FStar_TypeChecker_Cfg.allow_unbound_universes
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                           FStar_TypeChecker_Cfg.reify_ =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.reify_);
                                           FStar_TypeChecker_Cfg.compress_uvars
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.compress_uvars);
                                           FStar_TypeChecker_Cfg.no_full_norm
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.no_full_norm);
                                           FStar_TypeChecker_Cfg.check_no_uvars
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.check_no_uvars);
                                           FStar_TypeChecker_Cfg.unmeta =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.unmeta);
                                           FStar_TypeChecker_Cfg.unascribe =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.unascribe);
                                           FStar_TypeChecker_Cfg.in_full_norm_request
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.in_full_norm_request);
                                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                             = false;
                                           FStar_TypeChecker_Cfg.nbe_step =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.nbe_step);
                                           FStar_TypeChecker_Cfg.for_extraction
                                             =
                                             (uu___3161_23998.FStar_TypeChecker_Cfg.for_extraction)
                                         });
                                      FStar_TypeChecker_Cfg.tcenv =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.tcenv);
                                      FStar_TypeChecker_Cfg.debug =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.debug);
                                      FStar_TypeChecker_Cfg.delta_level =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.delta_level);
                                      FStar_TypeChecker_Cfg.primitive_steps =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.primitive_steps);
                                      FStar_TypeChecker_Cfg.strong =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.strong);
                                      FStar_TypeChecker_Cfg.memoize_lazy =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.memoize_lazy);
                                      FStar_TypeChecker_Cfg.normalize_pure_lets
                                        =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                      FStar_TypeChecker_Cfg.reifying =
                                        (uu___3159_23995.FStar_TypeChecker_Cfg.reifying)
                                    }) scrutinee_env [] scrutinee
                               else scrutinee in
                             let branches2 = norm_branches () in
                             let uu____24011 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (scrutinee1, branches2)) r in
                             rebuild cfg1 env2 stack2 uu____24011 in
                       maybe_commute_matches ()) in
                    let rec is_cons head =
                      let uu____24036 =
                        let uu____24037 = FStar_Syntax_Subst.compress head in
                        uu____24037.FStar_Syntax_Syntax.n in
                      match uu____24036 with
                      | FStar_Syntax_Syntax.Tm_uinst (h, uu____24041) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____24046 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24047;
                            FStar_Syntax_Syntax.fv_delta = uu____24048;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor);_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24049;
                            FStar_Syntax_Syntax.fv_delta = uu____24050;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____24051);_}
                          -> true
                      | uu____24058 -> false in
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
                      let uu____24222 =
                        FStar_Syntax_Util.head_and_args scrutinee2 in
                      match uu____24222 with
                      | (head, args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____24315 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____24354 ->
                                    let uu____24355 =
                                      let uu____24356 = is_cons head in
                                      Prims.op_Negation uu____24356 in
                                    FStar_Util.Inr uu____24355)
                           | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                               let uu____24381 =
                                 let uu____24382 =
                                   FStar_Syntax_Util.un_uinst head in
                                 uu____24382.FStar_Syntax_Syntax.n in
                               (match uu____24381 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____24400 ->
                                    let uu____24401 =
                                      let uu____24402 = is_cons head in
                                      Prims.op_Negation uu____24402 in
                                    FStar_Util.Inr uu____24401))
                    and matches_args out a p =
                      match (a, p) with
                      | ([], []) -> FStar_Util.Inl out
                      | ((t2, uu____24485)::rest_a,
                         (p1, uu____24488)::rest_p) ->
                          let uu____24542 = matches_pat t2 p1 in
                          (match uu____24542 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____24591 -> FStar_Util.Inr false in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1, wopt, b)::rest ->
                          let uu____24711 = matches_pat scrutinee1 p1 in
                          (match uu____24711 with
                           | FStar_Util.Inr (false) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____24751 ->
                                     let uu____24752 =
                                       FStar_Syntax_Print.pat_to_string p1 in
                                     let uu____24753 =
                                       let uu____24754 =
                                         FStar_List.map
                                           (fun uu____24764 ->
                                              match uu____24764 with
                                              | (uu____24769, t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s in
                                       FStar_All.pipe_right uu____24754
                                         (FStar_String.concat "; ") in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____24752 uu____24753);
                                (let env0 = env2 in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3 ->
                                        fun uu____24801 ->
                                          match uu____24801 with
                                          | (bv, t2) ->
                                              let uu____24824 =
                                                let uu____24831 =
                                                  let uu____24834 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv in
                                                  FStar_Pervasives_Native.Some
                                                    uu____24834 in
                                                let uu____24835 =
                                                  let uu____24836 =
                                                    let uu____24867 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2)) in
                                                    ([], t2, uu____24867,
                                                      false) in
                                                  Clos uu____24836 in
                                                (uu____24831, uu____24835) in
                                              uu____24824 :: env3) env2 s in
                                 let uu____24958 =
                                   guard_when_clause wopt b rest in
                                 norm cfg1 env3 stack2 uu____24958))) in
                    if
                      (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    then matches scrutinee branches1
                    else norm_and_rebuild_match ()))))
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
          FStar_TypeChecker_Cfg.log_cfg c
            (fun uu____24988 ->
               let uu____24989 = FStar_TypeChecker_Cfg.cfg_to_string c in
               FStar_Util.print1 "Cfg = %s\n" uu____24989);
          (let uu____24990 = is_nbe_request s in
           if uu____24990
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____24994 ->
                   let uu____24995 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____24995);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____24999 ->
                   let uu____25000 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25000);
              (let uu____25001 =
                 FStar_Util.record_time (fun uu____25007 -> nbe_eval c s t) in
               match uu____25001 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25014 ->
                         let uu____25015 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____25016 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25015 uu____25016);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25021 ->
                   let uu____25022 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____25022);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25026 ->
                   let uu____25027 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25027);
              (let uu____25028 =
                 FStar_Util.record_time (fun uu____25034 -> norm c [] [] t) in
               match uu____25028 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25047 ->
                         let uu____25048 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____25049 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25048 uu____25049);
                    r))))
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        let uu____25065 =
          let uu____25068 =
            let uu____25069 = FStar_TypeChecker_Env.current_module e in
            FStar_Ident.string_of_lid uu____25069 in
          FStar_Pervasives_Native.Some uu____25068 in
        FStar_Profiling.profile
          (fun uu____25071 -> normalize_with_primitive_steps [] s e t)
          uu____25065 "FStar.TypeChecker.Normalize"
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s ->
    fun e ->
      fun c ->
        let cfg = FStar_TypeChecker_Cfg.config s e in
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____25091 ->
             let uu____25092 = FStar_Syntax_Print.comp_to_string c in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____25092);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____25096 ->
             let uu____25097 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
             FStar_Util.print1 ">>> cfg = %s\n" uu____25097);
        (let uu____25098 =
           FStar_Util.record_time (fun uu____25104 -> norm_comp cfg [] c) in
         match uu____25098 with
         | (c1, ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____25117 ->
                   let uu____25118 = FStar_Syntax_Print.comp_to_string c1 in
                   let uu____25119 = FStar_Util.string_of_int ms in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____25118
                     uu____25119);
              c1))
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1 ->
    fun u ->
      let uu____25130 = FStar_TypeChecker_Cfg.config [] env1 in
      norm_universe uu____25130 [] u
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
      let uu____25150 = normalize steps env1 t in
      FStar_TypeChecker_Env.non_informative env1 uu____25150
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1 ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25161 -> c
      | FStar_Syntax_Syntax.GTotal (t, uopt) when non_info_norm env1 t ->
          let uu___3330_25180 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3330_25180.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3330_25180.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____25187 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ) in
          if uu____25187
          then
            let ct1 =
              let uu____25189 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name in
              match uu____25189 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____25196 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu____25196
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___3340_25200 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3340_25200.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3340_25200.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3340_25200.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c in
                  let uu___3344_25202 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3344_25202.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3344_25202.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3344_25202.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3344_25202.FStar_Syntax_Syntax.flags)
                  } in
            let uu___3347_25203 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3347_25203.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3347_25203.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25205 -> c
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1 ->
    fun lc ->
      let uu____25216 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ) in
      if uu____25216
      then
        let uu____25217 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name in
        match uu____25217 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3355_25221 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g -> g) lc in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3355_25221.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3355_25221.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3355_25221.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None -> lc
      else lc
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1 ->
    fun t ->
      let t1 =
        try
          (fun uu___3362_25237 ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3361_25240 ->
            ((let uu____25242 =
                let uu____25247 =
                  let uu____25248 = FStar_Util.message_of_exn uu___3361_25240 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25248 in
                (FStar_Errors.Warning_NormalizationFailure, uu____25247) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25242);
             t) in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1 ->
    fun c ->
      let c1 =
        try
          (fun uu___3372_25262 ->
             match () with
             | () ->
                 let uu____25263 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1 in
                 norm_comp uu____25263 [] c) ()
        with
        | uu___3371_25272 ->
            ((let uu____25274 =
                let uu____25279 =
                  let uu____25280 = FStar_Util.message_of_exn uu___3371_25272 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25280 in
                (FStar_Errors.Warning_NormalizationFailure, uu____25279) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25274);
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
                   let uu____25325 =
                     let uu____25326 =
                       let uu____25333 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi in
                       (y, uu____25333) in
                     FStar_Syntax_Syntax.Tm_refine uu____25326 in
                   FStar_Syntax_Syntax.mk uu____25325
                     t01.FStar_Syntax_Syntax.pos
               | uu____25338 -> t2)
          | uu____25339 -> t2 in
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
        let uu____25420 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____25420 with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu____25433 ->
                 let uu____25434 = FStar_Syntax_Util.abs_formals e in
                 (match uu____25434 with
                  | (actuals, uu____25444, uu____25445) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25463 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____25463 with
                         | (binders, args) ->
                             let uu____25474 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____25474
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
      | uu____25488 ->
          let uu____25489 = FStar_Syntax_Util.head_and_args t in
          (match uu____25489 with
           | (head, args) ->
               let uu____25532 =
                 let uu____25533 = FStar_Syntax_Subst.compress head in
                 uu____25533.FStar_Syntax_Syntax.n in
               (match uu____25532 with
                | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
                    let uu____25554 =
                      let uu____25561 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ in
                      FStar_Syntax_Util.arrow_formals uu____25561 in
                    (match uu____25554 with
                     | (formals, _tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25583 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3442_25591 = env1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3442_25591.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3442_25591.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3442_25591.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3442_25591.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3442_25591.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3442_25591.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3442_25591.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3442_25591.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3442_25591.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3442_25591.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3442_25591.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3442_25591.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3442_25591.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3442_25591.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3442_25591.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3442_25591.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3442_25591.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3442_25591.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3442_25591.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3442_25591.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3442_25591.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3442_25591.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3442_25591.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3442_25591.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3442_25591.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3442_25591.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3442_25591.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3442_25591.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3442_25591.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3442_25591.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3442_25591.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3442_25591.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3442_25591.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3442_25591.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3442_25591.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3442_25591.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3442_25591.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3442_25591.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3442_25591.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3442_25591.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3442_25591.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3442_25591.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3442_25591.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___3442_25591.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) t in
                            match uu____25583 with
                            | (uu____25592, ty, uu____25594) ->
                                eta_expand_with_type env1 t ty))
                | uu____25595 ->
                    let uu____25596 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3449_25604 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3449_25604.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3449_25604.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3449_25604.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3449_25604.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3449_25604.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3449_25604.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3449_25604.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3449_25604.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3449_25604.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3449_25604.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3449_25604.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3449_25604.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3449_25604.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3449_25604.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3449_25604.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3449_25604.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3449_25604.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3449_25604.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3449_25604.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3449_25604.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3449_25604.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3449_25604.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3449_25604.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3449_25604.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3449_25604.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3449_25604.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3449_25604.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3449_25604.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3449_25604.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3449_25604.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3449_25604.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3449_25604.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3449_25604.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3449_25604.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3449_25604.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3449_25604.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3449_25604.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3449_25604.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3449_25604.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3449_25604.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3449_25604.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3449_25604.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3449_25604.FStar_TypeChecker_Env.erasable_types_tab);
                           FStar_TypeChecker_Env.enable_defer_to_tac =
                             (uu___3449_25604.FStar_TypeChecker_Env.enable_defer_to_tac)
                         }) t in
                    (match uu____25596 with
                     | (uu____25605, ty, uu____25607) ->
                         eta_expand_with_type env1 t ty)))
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___3461_25688 = x in
      let uu____25689 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3461_25688.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3461_25688.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25689
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25692 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25707 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25708 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25709 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25710 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25717 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25718 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25719 -> t1
    | FStar_Syntax_Syntax.Tm_unknown -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu___3487_25753 = rc in
          let uu____25754 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____25763 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3487_25753.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25754;
            FStar_Syntax_Syntax.residual_flags = uu____25763
          } in
        let uu____25766 =
          let uu____25767 =
            let uu____25786 = elim_delayed_subst_binders bs in
            let uu____25795 = elim_delayed_subst_term t2 in
            let uu____25798 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____25786, uu____25795, uu____25798) in
          FStar_Syntax_Syntax.Tm_abs uu____25767 in
        mk uu____25766
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____25835 =
          let uu____25836 =
            let uu____25851 = elim_delayed_subst_binders bs in
            let uu____25860 = elim_delayed_subst_comp c in
            (uu____25851, uu____25860) in
          FStar_Syntax_Syntax.Tm_arrow uu____25836 in
        mk uu____25835
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu____25879 =
          let uu____25880 =
            let uu____25887 = elim_bv bv in
            let uu____25888 = elim_delayed_subst_term phi in
            (uu____25887, uu____25888) in
          FStar_Syntax_Syntax.Tm_refine uu____25880 in
        mk uu____25879
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu____25919 =
          let uu____25920 =
            let uu____25937 = elim_delayed_subst_term t2 in
            let uu____25940 = elim_delayed_subst_args args in
            (uu____25937, uu____25940) in
          FStar_Syntax_Syntax.Tm_app uu____25920 in
        mk uu____25919
    | FStar_Syntax_Syntax.Tm_match (t2, branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3509_26012 = p in
              let uu____26013 =
                let uu____26014 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____26014 in
              {
                FStar_Syntax_Syntax.v = uu____26013;
                FStar_Syntax_Syntax.p =
                  (uu___3509_26012.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3513_26016 = p in
              let uu____26017 =
                let uu____26018 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____26018 in
              {
                FStar_Syntax_Syntax.v = uu____26017;
                FStar_Syntax_Syntax.p =
                  (uu___3513_26016.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___3519_26025 = p in
              let uu____26026 =
                let uu____26027 =
                  let uu____26034 = elim_bv x in
                  let uu____26035 = elim_delayed_subst_term t0 in
                  (uu____26034, uu____26035) in
                FStar_Syntax_Syntax.Pat_dot_term uu____26027 in
              {
                FStar_Syntax_Syntax.v = uu____26026;
                FStar_Syntax_Syntax.p =
                  (uu___3519_26025.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___3525_26058 = p in
              let uu____26059 =
                let uu____26060 =
                  let uu____26073 =
                    FStar_List.map
                      (fun uu____26096 ->
                         match uu____26096 with
                         | (x, b) ->
                             let uu____26109 = elim_pat x in (uu____26109, b))
                      pats in
                  (fv, uu____26073) in
                FStar_Syntax_Syntax.Pat_cons uu____26060 in
              {
                FStar_Syntax_Syntax.v = uu____26059;
                FStar_Syntax_Syntax.p =
                  (uu___3525_26058.FStar_Syntax_Syntax.p)
              }
          | uu____26122 -> p in
        let elim_branch uu____26146 =
          match uu____26146 with
          | (pat, wopt, t3) ->
              let uu____26172 = elim_pat pat in
              let uu____26175 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____26178 = elim_delayed_subst_term t3 in
              (uu____26172, uu____26175, uu____26178) in
        let uu____26183 =
          let uu____26184 =
            let uu____26207 = elim_delayed_subst_term t2 in
            let uu____26210 = FStar_List.map elim_branch branches1 in
            (uu____26207, uu____26210) in
          FStar_Syntax_Syntax.Tm_match uu____26184 in
        mk uu____26183
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let elim_ascription uu____26341 =
          match uu____26341 with
          | (tc, topt) ->
              let uu____26376 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26386 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____26386
                | FStar_Util.Inr c ->
                    let uu____26388 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____26388 in
              let uu____26389 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____26376, uu____26389) in
        let uu____26398 =
          let uu____26399 =
            let uu____26426 = elim_delayed_subst_term t2 in
            let uu____26429 = elim_ascription a in
            (uu____26426, uu____26429, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____26399 in
        mk uu____26398
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu___3555_26490 = lb in
          let uu____26491 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____26494 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3555_26490.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3555_26490.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26491;
            FStar_Syntax_Syntax.lbeff =
              (uu___3555_26490.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26494;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3555_26490.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3555_26490.FStar_Syntax_Syntax.lbpos)
          } in
        let uu____26497 =
          let uu____26498 =
            let uu____26511 =
              let uu____26518 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____26518) in
            let uu____26527 = elim_delayed_subst_term t2 in
            (uu____26511, uu____26527) in
          FStar_Syntax_Syntax.Tm_let uu____26498 in
        mk uu____26497
    | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
        mk (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi in
        let uu____26571 =
          let uu____26572 =
            let uu____26579 = elim_delayed_subst_term tm in
            (uu____26579, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu____26572 in
        mk uu____26571
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu____26590 =
          let uu____26591 =
            let uu____26598 = elim_delayed_subst_term t2 in
            let uu____26601 = elim_delayed_subst_meta md in
            (uu____26598, uu____26601) in
          FStar_Syntax_Syntax.Tm_meta uu____26591 in
        mk uu____26590
and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_List.map
      (fun uu___17_26610 ->
         match uu___17_26610 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26614 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____26614
         | f -> f) flags
and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c ->
    let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uopt) ->
        let uu____26637 =
          let uu____26638 =
            let uu____26647 = elim_delayed_subst_term t in
            (uu____26647, uopt) in
          FStar_Syntax_Syntax.Total uu____26638 in
        mk uu____26637
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uu____26664 =
          let uu____26665 =
            let uu____26674 = elim_delayed_subst_term t in
            (uu____26674, uopt) in
          FStar_Syntax_Syntax.GTotal uu____26665 in
        mk uu____26664
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3588_26683 = ct in
          let uu____26684 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____26687 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____26698 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3588_26683.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3588_26683.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26684;
            FStar_Syntax_Syntax.effect_args = uu____26687;
            FStar_Syntax_Syntax.flags = uu____26698
          } in
        mk (FStar_Syntax_Syntax.Comp ct1)
and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_26701 ->
    match uu___18_26701 with
    | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
        let uu____26736 =
          let uu____26757 = FStar_List.map elim_delayed_subst_term names in
          let uu____26766 = FStar_List.map elim_delayed_subst_args args in
          (uu____26757, uu____26766) in
        FStar_Syntax_Syntax.Meta_pattern uu____26736
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____26821 =
          let uu____26828 = elim_delayed_subst_term t in (m, uu____26828) in
        FStar_Syntax_Syntax.Meta_monadic uu____26821
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu____26840 =
          let uu____26849 = elim_delayed_subst_term t in
          (m1, m2, uu____26849) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26840
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
      (fun uu____26882 ->
         match uu____26882 with
         | (t, q) ->
             let uu____26901 = elim_delayed_subst_term t in (uu____26901, q))
      args
and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun uu____26929 ->
         match uu____26929 with
         | (x, q) ->
             let uu____26948 =
               let uu___3614_26949 = x in
               let uu____26950 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3614_26949.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3614_26949.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26950
               } in
             (uu____26948, q)) bs
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
            | (uu____27056, FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  c.FStar_Syntax_Syntax.pos
            | (uu____27088, FStar_Util.Inl t) ->
                let uu____27110 =
                  let uu____27111 =
                    let uu____27126 = FStar_Syntax_Syntax.mk_Total t in
                    (binders, uu____27126) in
                  FStar_Syntax_Syntax.Tm_arrow uu____27111 in
                FStar_Syntax_Syntax.mk uu____27110 t.FStar_Syntax_Syntax.pos in
          let uu____27139 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____27139 with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env1 t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____27171 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27244 ->
                    let uu____27245 =
                      let uu____27254 =
                        let uu____27255 = FStar_Syntax_Subst.compress t4 in
                        uu____27255.FStar_Syntax_Syntax.n in
                      (uu____27254, tc) in
                    (match uu____27245 with
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inr uu____27284) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inl uu____27331) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____27376, FStar_Util.Inl uu____27377) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____27408 -> failwith "Impossible") in
              (match uu____27171 with
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
          let uu____27545 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t) in
          match uu____27545 with
          | (univ_names1, binders1, tc) ->
              let uu____27619 = FStar_Util.left tc in
              (univ_names1, binders1, uu____27619)
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
          let uu____27672 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c) in
          match uu____27672 with
          | (univ_names1, binders1, tc) ->
              let uu____27746 = FStar_Util.right tc in
              (univ_names1, binders1, uu____27746)
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1 ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univ_names, binders, typ, lids, lids') ->
          let uu____27787 = elim_uvars_aux_t env1 univ_names binders typ in
          (match uu____27787 with
           | (univ_names1, binders1, typ1) ->
               let uu___3697_27827 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3697_27827.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3697_27827.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3697_27827.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3697_27827.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3697_27827.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
          let uu___3703_27842 = s in
          let uu____27843 =
            let uu____27844 =
              let uu____27853 = FStar_List.map (elim_uvars env1) sigs in
              (uu____27853, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____27844 in
          {
            FStar_Syntax_Syntax.sigel = uu____27843;
            FStar_Syntax_Syntax.sigrng =
              (uu___3703_27842.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3703_27842.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3703_27842.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3703_27842.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3703_27842.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univ_names, typ, lident, i, lids) ->
          let uu____27870 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____27870 with
           | (univ_names1, uu____27894, typ1) ->
               let uu___3717_27916 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3717_27916.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3717_27916.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3717_27916.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3717_27916.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3717_27916.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) ->
          let uu____27922 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____27922 with
           | (univ_names1, uu____27946, typ1) ->
               let uu___3728_27968 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3728_27968.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3728_27968.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3728_27968.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3728_27968.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3728_27968.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____27996 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____27996 with
                    | (opening, lbunivs) ->
                        let elim t =
                          let uu____28021 =
                            let uu____28022 =
                              let uu____28023 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env1 uu____28023 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28022 in
                          elim_delayed_subst_term uu____28021 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___3744_28026 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3744_28026.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3744_28026.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3744_28026.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3744_28026.FStar_Syntax_Syntax.lbpos)
                        })) in
          let uu___3747_28027 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3747_28027.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3747_28027.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3747_28027.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3747_28027.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3747_28027.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l, us, t) ->
          let uu____28035 = elim_uvars_aux_t env1 us [] t in
          (match uu____28035 with
           | (us1, uu____28059, t1) ->
               let uu___3758_28081 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3758_28081.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3758_28081.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3758_28081.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3758_28081.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3758_28081.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28083 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit in
          (match uu____28083 with
           | (univs, binders, uu____28102) ->
               let uu____28123 =
                 let uu____28128 = FStar_Syntax_Subst.univ_var_opening univs in
                 match uu____28128 with
                 | (univs_opening, univs1) ->
                     let uu____28151 =
                       FStar_Syntax_Subst.univ_var_closing univs1 in
                     (univs_opening, uu____28151) in
               (match uu____28123 with
                | (univs_opening, univs_closing) ->
                    let uu____28154 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____28160 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____28161 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____28160, uu____28161) in
                    (match uu____28154 with
                     | (b_opening, b_closing) ->
                         let n = FStar_List.length univs in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____28187 =
                           match uu____28187 with
                           | (us, t) ->
                               let n_us = FStar_List.length us in
                               let uu____28205 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____28205 with
                                | (us1, t1) ->
                                    let uu____28216 =
                                      let uu____28225 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____28230 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____28225, uu____28230) in
                                    (match uu____28216 with
                                     | (b_opening1, b_closing1) ->
                                         let uu____28253 =
                                           let uu____28262 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           let uu____28267 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           (uu____28262, uu____28267) in
                                         (match uu____28253 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28291 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28291 in
                                              let uu____28292 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2 in
                                              (match uu____28292 with
                                               | (uu____28319, uu____28320,
                                                  t3) ->
                                                   let t4 =
                                                     let uu____28343 =
                                                       let uu____28344 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28344 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28343 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____28353 =
                             elim_uvars_aux_t env1 univs binders t in
                           match uu____28353 with
                           | (uu____28372, uu____28373, t1) -> t1 in
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
                             | uu____28449 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____28476 =
                               let uu____28477 =
                                 FStar_Syntax_Subst.compress body in
                               uu____28477.FStar_Syntax_Syntax.n in
                             match uu____28476 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,
                                  (FStar_Util.Inl typ,
                                   FStar_Pervasives_Native.None),
                                  FStar_Pervasives_Native.None)
                                 -> (defn, typ)
                             | uu____28536 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____28569 =
                               let uu____28570 =
                                 FStar_Syntax_Subst.compress t in
                               uu____28570.FStar_Syntax_Syntax.n in
                             match uu____28569 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars, body, uu____28593) ->
                                 let uu____28618 = destruct_action_body body in
                                 (match uu____28618 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu____28667 ->
                                 let uu____28668 = destruct_action_body t in
                                 (match uu____28668 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu____28723 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____28723 with
                           | (action_univs, t) ->
                               let uu____28732 = destruct_action_typ_templ t in
                               (match uu____28732 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      let uu___3842_28779 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3842_28779.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3842_28779.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3845_28781 = ed in
                           let uu____28782 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature in
                           let uu____28783 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu____28784 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3845_28781.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3845_28781.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____28782;
                             FStar_Syntax_Syntax.combinators = uu____28783;
                             FStar_Syntax_Syntax.actions = uu____28784;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3845_28781.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let uu___3848_28787 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3848_28787.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3848_28787.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3848_28787.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3848_28787.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3848_28787.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_28808 =
            match uu___19_28808 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu____28839 = elim_uvars_aux_t env1 us [] t in
                (match uu____28839 with
                 | (us1, uu____28871, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___3863_28902 = sub_eff in
            let uu____28903 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____28906 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___3863_28902.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3863_28902.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28903;
              FStar_Syntax_Syntax.lift = uu____28906
            } in
          let uu___3866_28909 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3866_28909.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3866_28909.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3866_28909.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3866_28909.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3866_28909.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, univ_names, binders, comp, flags) ->
          let uu____28919 = elim_uvars_aux_c env1 univ_names binders comp in
          (match uu____28919 with
           | (univ_names1, binders1, comp1) ->
               let uu___3879_28959 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3879_28959.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3879_28959.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3879_28959.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3879_28959.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3879_28959.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28962 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____28963 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28974 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m, n, p, (us_t, t), (us_ty, ty)) ->
          let uu____29004 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____29004 with
           | (us_t1, uu____29028, t1) ->
               let uu____29050 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____29050 with
                | (us_ty1, uu____29074, ty1) ->
                    let uu___3906_29096 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3906_29096.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3906_29096.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3906_29096.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3906_29096.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3906_29096.FStar_Syntax_Syntax.sigopts)
                    }))
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          (m, n, (us_t, t), (us_ty, ty)) ->
          let uu____29127 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____29127 with
           | (us_t1, uu____29151, t1) ->
               let uu____29173 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____29173 with
                | (us_ty1, uu____29197, ty1) ->
                    let uu___3926_29219 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                           (m, n, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3926_29219.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3926_29219.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3926_29219.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3926_29219.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3926_29219.FStar_Syntax_Syntax.sigopts)
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
        let uu____29268 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu____29268 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____29290 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
            (match uu____29290 with
             | (uu____29297, head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     t.FStar_Syntax_Syntax.pos in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env1 t' in
                 FStar_Pervasives_Native.Some t'1) in
      let uu____29301 = FStar_Syntax_Util.head_and_args t in
      match uu____29301 with
      | (head, args) ->
          let uu____29346 =
            let uu____29347 = FStar_Syntax_Subst.compress head in
            uu____29347.FStar_Syntax_Syntax.n in
          (match uu____29346 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____29354;
                  FStar_Syntax_Syntax.vars = uu____29355;_},
                us)
               -> aux fv us args
           | uu____29361 -> FStar_Pervasives_Native.None)
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
          let uu____29417 = FStar_Syntax_Util.arrow_formals_comp t1 in
          match uu____29417 with
          | (bs, c) ->
              let len = FStar_List.length bs in
              (match (bs, c) with
               | ([], uu____29453) when retry ->
                   let uu____29472 = unfold_whnf env1 t1 in
                   aux false n1 uu____29472
               | ([], uu____29473) when Prims.op_Negation retry -> (bs, c)
               | (bs1, c1) when len = n1 -> (bs1, c1)
               | (bs1, c1) when len > n1 ->
                   let uu____29540 = FStar_List.splitAt n1 bs1 in
                   (match uu____29540 with
                    | (bs_l, bs_r) ->
                        let uu____29607 =
                          let uu____29608 = FStar_Syntax_Util.arrow bs_r c1 in
                          FStar_Syntax_Syntax.mk_Total uu____29608 in
                        (bs_l, uu____29607))
               | (bs1, c1) when
                   ((len < n1) && (FStar_Syntax_Util.is_total_comp c1)) &&
                     (let uu____29634 = FStar_Syntax_Util.has_decreases c1 in
                      Prims.op_Negation uu____29634)
                   ->
                   let uu____29635 =
                     aux true (n1 - len) (FStar_Syntax_Util.comp_result c1) in
                   (match uu____29635 with
                    | (bs', c') -> ((FStar_List.append bs1 bs'), c'))
               | (bs1, c1) -> (bs1, c1)) in
        aux true n t