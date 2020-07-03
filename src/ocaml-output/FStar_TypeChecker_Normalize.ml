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
    match projectee with | Clos _0 -> true | uu____121 -> false
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee -> match projectee with | Clos _0 -> _0
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee ->
    match projectee with | Univ _0 -> true | uu____233 -> false
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee -> match projectee with | Dummy -> true | uu____251 -> false
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
  fun projectee -> match projectee with | Arg _0 -> true | uu____425 -> false
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivArgs _0 -> true | uu____468 -> false
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | MemoLazy _0 -> true | uu____511 -> false
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____556 -> false
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu____611 -> false
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu____674 -> false
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | App _0 -> _0
let (uu___is_CBVApp : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | CBVApp _0 -> true | uu____725 -> false
let (__proj__CBVApp__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | CBVApp _0 -> _0
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____774 -> false
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu____819 -> false
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Cfg _0 -> true | uu____862 -> false
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee -> match projectee with | Cfg _0 -> _0
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Debug _0 -> true | uu____885 -> false
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____914 = FStar_Syntax_Util.head_and_args' t in
    match uu____914 with | (hd, uu____930) -> hd
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg ->
    fun r ->
      fun t ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu____981 = FStar_ST.op_Bang r in
          match uu____981 with
          | FStar_Pervasives_Native.Some uu____1007 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let (closure_to_string : closure -> Prims.string) =
  fun uu___1_1040 ->
    match uu___1_1040 with
    | Clos (env1, t, uu____1044, uu____1045) ->
        let uu____1092 =
          FStar_All.pipe_right (FStar_List.length env1)
            FStar_Util.string_of_int in
        let uu____1102 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1092 uu____1102
    | Univ uu____1105 -> "Univ"
    | Dummy -> "dummy"
let (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env1 ->
    let uu____1131 =
      FStar_List.map
        (fun uu____1147 ->
           match uu____1147 with
           | (bopt, c) ->
               let uu____1161 =
                 match bopt with
                 | FStar_Pervasives_Native.None -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x in
               let uu____1166 = closure_to_string c in
               FStar_Util.format2 "(%s, %s)" uu____1161 uu____1166) env1 in
    FStar_All.pipe_right uu____1131 (FStar_String.concat "; ")
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1180 ->
    match uu___2_1180 with
    | Arg (c, uu____1183, uu____1184) ->
        let uu____1185 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1185
    | MemoLazy uu____1188 -> "MemoLazy"
    | Abs (uu____1196, bs, uu____1198, uu____1199, uu____1200) ->
        let uu____1205 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1205
    | UnivArgs uu____1216 -> "UnivArgs"
    | Match uu____1224 -> "Match"
    | App (uu____1234, t, uu____1236, uu____1237) ->
        let uu____1238 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1238
    | CBVApp (uu____1241, t, uu____1243, uu____1244) ->
        let uu____1245 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "CBVApp %s" uu____1245
    | Meta (uu____1248, m, uu____1250) -> "Meta"
    | Let uu____1252 -> "Let"
    | Cfg uu____1262 -> "Cfg"
    | Debug (t, uu____1265) ->
        let uu____1266 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1266
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s ->
    let uu____1280 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1280 (FStar_String.concat "; ")
let is_empty : 'uuuuuu1295 . 'uuuuuu1295 Prims.list -> Prims.bool =
  fun uu___3_1303 ->
    match uu___3_1303 with | [] -> true | uu____1307 -> false
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env1 ->
    fun x ->
      try
        (fun uu___119_1340 ->
           match () with
           | () ->
               let uu____1341 =
                 FStar_List.nth env1 x.FStar_Syntax_Syntax.index in
               FStar_Pervasives_Native.snd uu____1341) ()
      with
      | uu___118_1358 ->
          let uu____1359 =
            let uu____1361 = FStar_Syntax_Print.db_to_string x in
            let uu____1363 = env_to_string env1 in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1361
              uu____1363 in
          failwith uu____1359
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l ->
    let uu____1374 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid in
    if uu____1374
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1381 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid in
       if uu____1381
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1388 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid in
          if uu____1388
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
          let uu____1426 =
            FStar_List.fold_left
              (fun uu____1452 ->
                 fun u1 ->
                   match uu____1452 with
                   | (cur_kernel, cur_max, out) ->
                       let uu____1477 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1477 with
                        | (k_u, n) ->
                            let uu____1495 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1495
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1426 with
          | (uu____1516, u1, out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___153_1544 ->
                    match () with
                    | () ->
                        let uu____1547 =
                          let uu____1548 = FStar_List.nth env1 x in
                          FStar_Pervasives_Native.snd uu____1548 in
                        (match uu____1547 with
                         | Univ u3 ->
                             ((let uu____1567 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm") in
                               if uu____1567
                               then
                                 let uu____1572 =
                                   FStar_Syntax_Print.univ_to_string u3 in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1572
                               else ());
                              aux u3)
                         | Dummy -> [u2]
                         | uu____1577 ->
                             let uu____1578 =
                               let uu____1580 = FStar_Util.string_of_int x in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1580 in
                             failwith uu____1578)) ()
               with
               | uu____1590 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1596 =
                        let uu____1598 = FStar_Util.string_of_int x in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1598 in
                      failwith uu____1596))
          | FStar_Syntax_Syntax.U_unif uu____1603 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1614 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1625 -> [u2]
          | FStar_Syntax_Syntax.U_unknown -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1632 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1632 norm_univs_for_max in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest in
                   let uu____1649 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1649 with
                    | (FStar_Syntax_Syntax.U_zero, n) ->
                        let uu____1660 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3 ->
                                  let uu____1670 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1670 with
                                  | (uu____1677, m) -> n <= m)) in
                        if uu____1660 then rest1 else us1
                    | uu____1686 -> us1)
               | uu____1692 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1696 = aux u3 in
              FStar_List.map
                (fun uu____1699 -> FStar_Syntax_Syntax.U_succ uu____1699)
                uu____1696 in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1703 = aux u in
           match uu____1703 with
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
            (fun uu____1864 ->
               let uu____1865 = FStar_Syntax_Print.tag_of_term t in
               let uu____1867 = env_to_string env1 in
               let uu____1869 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print3 ">>> %s (env=%s)\nClosure_as_term %s\n"
                 uu____1865 uu____1867 uu____1869);
          (match env1 with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env1 stack1 t
           | uu____1882 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1885 ->
                    let uu____1900 = FStar_Syntax_Subst.compress t in
                    inline_closure_env cfg env1 stack1 uu____1900
                | FStar_Syntax_Syntax.Tm_unknown ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_constant uu____1901 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_name uu____1902 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_lazy uu____1903 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_fvar uu____1904 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1929 ->
                           let uu____1942 =
                             let uu____1944 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos in
                             let uu____1946 =
                               FStar_Syntax_Print.term_to_string t1 in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1944 uu____1946 in
                           failwith uu____1942
                       | uu____1951 -> inline_closure_env cfg env1 stack1 t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1 ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_1987 ->
                                         match uu___4_1987 with
                                         | FStar_Syntax_Syntax.NT (x, t1) ->
                                             let uu____1994 =
                                               let uu____2001 =
                                                 inline_closure_env cfg env1
                                                   [] t1 in
                                               (x, uu____2001) in
                                             FStar_Syntax_Syntax.NT
                                               uu____1994
                                         | FStar_Syntax_Syntax.NM (x, i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___247_2013 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___247_2013.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___247_2013.FStar_Syntax_Syntax.sort)
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
                                              | uu____2019 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____2022 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes")))) in
                       let t1 =
                         let uu___256_2027 = t in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___256_2027.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___256_2027.FStar_Syntax_Syntax.vars)
                         } in
                       rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2048 =
                        let uu____2049 = norm_universe cfg env1 u in
                        FStar_Syntax_Syntax.Tm_type uu____2049 in
                      FStar_Syntax_Syntax.mk uu____2048
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
                    let t1 =
                      let uu____2057 =
                        FStar_List.map (norm_universe cfg env1) us in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2057 in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2059 = lookup_bvar env1 x in
                    (match uu____2059 with
                     | Univ uu____2062 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy ->
                         let x1 =
                           let uu___272_2067 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___272_2067.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___272_2067.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1
                     | Clos (env2, t0, uu____2073, uu____2074) ->
                         inline_closure_env cfg env2 stack1 t0)
                | FStar_Syntax_Syntax.Tm_app (head, args) ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____2165 ->
                              fun stack2 ->
                                match uu____2165 with
                                | (a, aq) ->
                                    let uu____2177 =
                                      let uu____2178 =
                                        let uu____2185 =
                                          let uu____2186 =
                                            let uu____2218 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu____2218, false) in
                                          Clos uu____2186 in
                                        (uu____2185, aq,
                                          (t.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____2178 in
                                    uu____2177 :: stack2) args) in
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
                    let uu____2386 = close_binders cfg env1 bs in
                    (match uu____2386 with
                     | (bs1, env') ->
                         let c1 = close_comp cfg env' c in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_refine (x, uu____2436) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env1 stack1
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
                    let uu____2447 =
                      let uu____2460 =
                        let uu____2469 = FStar_Syntax_Syntax.mk_binder x in
                        [uu____2469] in
                      close_binders cfg env1 uu____2460 in
                    (match uu____2447 with
                     | (x1, env2) ->
                         let phi1 = non_tail_inline_closure_env cfg env2 phi in
                         let t1 =
                           let uu____2514 =
                             let uu____2515 =
                               let uu____2522 =
                                 let uu____2523 = FStar_List.hd x1 in
                                 FStar_All.pipe_right uu____2523
                                   FStar_Pervasives_Native.fst in
                               (uu____2522, phi1) in
                             FStar_Syntax_Syntax.Tm_refine uu____2515 in
                           FStar_Syntax_Syntax.mk uu____2514
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env2 stack1 t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt)
                    ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2622 =
                            non_tail_inline_closure_env cfg env1 t2 in
                          FStar_Util.Inl uu____2622
                      | FStar_Util.Inr c ->
                          let uu____2636 = close_comp cfg env1 c in
                          FStar_Util.Inr uu____2636 in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env1) in
                    let t2 =
                      let uu____2655 =
                        let uu____2656 =
                          let uu____2683 =
                            non_tail_inline_closure_env cfg env1 t1 in
                          (uu____2683, (annot1, tacopt1), lopt) in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2656 in
                      FStar_Syntax_Syntax.mk uu____2655
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t2
                | FStar_Syntax_Syntax.Tm_quoted (t', qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic ->
                          let uu____2729 =
                            let uu____2730 =
                              let uu____2737 =
                                non_tail_inline_closure_env cfg env1 t' in
                              (uu____2737, qi) in
                            FStar_Syntax_Syntax.Tm_quoted uu____2730 in
                          FStar_Syntax_Syntax.mk uu____2729
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
                        (fun env2 -> fun uu____2792 -> dummy :: env2) env1
                        lb.FStar_Syntax_Syntax.lbunivs in
                    let typ =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let def =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbdef in
                    let uu____2813 =
                      let uu____2824 = FStar_Syntax_Syntax.is_top_level [lb] in
                      if uu____2824
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         let uu____2846 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body in
                         ((FStar_Util.Inl
                             (let uu___364_2862 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___364_2862.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___364_2862.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2846)) in
                    (match uu____2813 with
                     | (nm, body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs in
                         let lb1 =
                           let uu___370_2889 = lb in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___370_2889.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___370_2889.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___370_2889.FStar_Syntax_Syntax.lbpos)
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env0 stack1 t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2906, lbs), body) ->
                    let norm_one_lb env2 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2972 -> fun env3 -> dummy :: env3)
                          lb.FStar_Syntax_Syntax.lbunivs env2 in
                      let env3 =
                        let uu____2989 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu____2989
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____3004 -> fun env3 -> dummy :: env3) lbs
                            env_univs in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp in
                      let nm =
                        let uu____3028 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu____3028
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           FStar_Util.Inl
                             (let uu___393_3039 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___393_3039.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___393_3039.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              })) in
                      let uu___396_3040 = lb in
                      let uu____3041 =
                        non_tail_inline_closure_env cfg env3
                          lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___396_3040.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___396_3040.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3041;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___396_3040.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___396_3040.FStar_Syntax_Syntax.lbpos)
                      } in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env1)) in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3073 -> fun env2 -> dummy :: env2) lbs1
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
            (fun uu____3165 ->
               let uu____3166 = FStar_Syntax_Print.tag_of_term t in
               let uu____3168 = env_to_string env1 in
               let uu____3170 = stack_to_string stack1 in
               let uu____3172 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu____3166 uu____3168 uu____3170 uu____3172);
          (match stack1 with
           | [] -> t
           | (Arg
               (Clos (env_arg, tm, uu____3179, uu____3180), aq, r))::stack2
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
               let uu____3271 = close_binders cfg env' bs in
               (match uu____3271 with
                | (bs1, uu____3287) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt in
                    let uu____3307 =
                      let uu___463_3310 = FStar_Syntax_Util.abs bs1 t lopt1 in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___463_3310.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___463_3310.FStar_Syntax_Syntax.vars)
                      } in
                    rebuild_closure cfg env1 stack2 uu____3307)
           | (Match (env2, branches1, cfg1, r))::stack2 ->
               let close_one_branch env3 uu____3366 =
                 match uu____3366 with
                 | (pat, w_opt, tm) ->
                     let rec norm_pat env4 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3481 ->
                           (p, env4)
                       | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                           let uu____3512 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3601 ->
                                     fun uu____3602 ->
                                       match (uu____3601, uu____3602) with
                                       | ((pats1, env5), (p1, b)) ->
                                           let uu____3752 = norm_pat env5 p1 in
                                           (match uu____3752 with
                                            | (p2, env6) ->
                                                (((p2, b) :: pats1), env6)))
                                  ([], env4)) in
                           (match uu____3512 with
                            | (pats1, env5) ->
                                ((let uu___500_3922 = p in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___500_3922.FStar_Syntax_Syntax.p)
                                  }), env5))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___504_3943 = x in
                             let uu____3944 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___504_3943.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___504_3943.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3944
                             } in
                           ((let uu___507_3958 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___507_3958.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___511_3969 = x in
                             let uu____3970 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___511_3969.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___511_3969.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3970
                             } in
                           ((let uu___514_3984 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___514_3984.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_dot_term (x, t1) ->
                           let x1 =
                             let uu___520_4000 = x in
                             let uu____4001 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___520_4000.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___520_4000.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4001
                             } in
                           let t2 = non_tail_inline_closure_env cfg1 env4 t1 in
                           ((let uu___524_4018 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___524_4018.FStar_Syntax_Syntax.p)
                             }), env4) in
                     let uu____4023 = norm_pat env3 pat in
                     (match uu____4023 with
                      | (pat1, env4) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4092 =
                                  non_tail_inline_closure_env cfg1 env4 w in
                                FStar_Pervasives_Native.Some uu____4092 in
                          let tm1 = non_tail_inline_closure_env cfg1 env4 tm in
                          (pat1, w_opt1, tm1)) in
               let t1 =
                 let uu____4111 =
                   let uu____4112 =
                     let uu____4135 =
                       FStar_All.pipe_right branches1
                         (FStar_List.map (close_one_branch env2)) in
                     (t, uu____4135) in
                   FStar_Syntax_Syntax.Tm_match uu____4112 in
                 FStar_Syntax_Syntax.mk uu____4111 t.FStar_Syntax_Syntax.pos in
               rebuild_closure cfg1 env2 stack2 t1
           | (Meta (env_m, m, r))::stack2 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
                     let uu____4271 =
                       let uu____4292 =
                         FStar_All.pipe_right names
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m)) in
                       let uu____4309 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1 ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4418 ->
                                         match uu____4418 with
                                         | (a, q) ->
                                             let uu____4445 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a in
                                             (uu____4445, q))))) in
                       (uu____4292, uu____4309) in
                     FStar_Syntax_Syntax.Meta_pattern uu____4271
                 | FStar_Syntax_Syntax.Meta_monadic (m1, tbody) ->
                     let uu____4474 =
                       let uu____4481 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m1, uu____4481) in
                     FStar_Syntax_Syntax.Meta_monadic uu____4474
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) ->
                     let uu____4493 =
                       let uu____4502 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m1, m2, uu____4502) in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4493
                 | uu____4507 -> m in
               let t1 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (t, m1))
                   r in
               rebuild_closure cfg env1 stack2 t1
           | uu____4513 -> failwith "Impossible: unexpected stack element")
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
            let uu____4529 =
              let uu____4530 =
                let uu____4531 = inline_closure_env cfg env1 [] t in
                FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____4531 in
              FStar_Syntax_Syntax.Meta uu____4530 in
            FStar_Pervasives_Native.Some uu____4529
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
            let uu____4537 =
              let uu____4538 =
                let uu____4539 = inline_closure_env cfg env1 [] t in
                FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____4539 in
              FStar_Syntax_Syntax.Meta uu____4538 in
            FStar_Pervasives_Native.Some uu____4537
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
        let uu____4556 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4640 ->
                  fun uu____4641 ->
                    match (uu____4640, uu____4641) with
                    | ((env2, out), (b, imp)) ->
                        let b1 =
                          let uu___584_4781 = b in
                          let uu____4782 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___584_4781.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___584_4781.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4782
                          } in
                        let imp1 = close_imp cfg env2 imp in
                        let env3 = dummy :: env2 in
                        (env3, ((b1, imp1) :: out))) (env1, [])) in
        match uu____4556 with | (env2, bs1) -> ((FStar_List.rev bs1), env2)
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
        | uu____4924 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t, uopt) ->
                 let uu____4937 = inline_closure_env cfg env1 [] t in
                 let uu____4938 =
                   FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____4937 uu____4938
             | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                 let uu____4951 = inline_closure_env cfg env1 [] t in
                 let uu____4952 =
                   FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4951 uu____4952
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5006 ->
                           match uu____5006 with
                           | (a, q) ->
                               let uu____5027 =
                                 inline_closure_env cfg env1 [] a in
                               (uu____5027, q))) in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5044 ->
                           match uu___5_5044 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5048 =
                                 inline_closure_env cfg env1 [] t in
                               FStar_Syntax_Syntax.DECREASES uu____5048
                           | f -> f)) in
                 let uu____5052 =
                   let uu___617_5053 = c1 in
                   let uu____5054 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5054;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___617_5053.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____5052)
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
                   (fun uu___6_5072 ->
                      match uu___6_5072 with
                      | FStar_Syntax_Syntax.DECREASES uu____5074 -> false
                      | uu____5078 -> true)) in
            let rc1 =
              let uu___629_5081 = rc in
              let uu____5082 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___629_5081.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5082;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____5091 -> lopt
let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5112 ->
            match uu___7_5112 with
            | FStar_Syntax_Syntax.DECREASES uu____5114 -> false
            | uu____5118 -> true))
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
    let uu____5165 = FStar_ST.op_Bang unembed_binder_knot in
    match uu____5165 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5204 = FStar_Syntax_Embeddings.unembed e t in
        uu____5204 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
let mk_psc_subst :
  'uuuuuu5224 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'uuuuuu5224) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg ->
    fun env1 ->
      FStar_List.fold_right
        (fun uu____5286 ->
           fun subst ->
             match uu____5286 with
             | (binder_opt, closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b, Clos
                     (env2, term, uu____5327, uu____5328)) ->
                      let uu____5389 = b in
                      (match uu____5389 with
                       | (bv, uu____5397) ->
                           let uu____5398 =
                             let uu____5400 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid in
                             Prims.op_Negation uu____5400 in
                           if uu____5398
                           then subst
                           else
                             (let term1 = closure_as_term cfg env2 term in
                              let uu____5408 = unembed_binder term1 in
                              match uu____5408 with
                              | FStar_Pervasives_Native.None -> subst
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5415 =
                                      let uu___669_5416 = bv in
                                      let uu____5417 =
                                        FStar_Syntax_Subst.subst subst
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___669_5416.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___669_5416.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5417
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____5415 in
                                  let b_for_x =
                                    let uu____5423 =
                                      let uu____5430 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5430) in
                                    FStar_Syntax_Syntax.NT uu____5423 in
                                  let subst1 =
                                    FStar_List.filter
                                      (fun uu___8_5446 ->
                                         match uu___8_5446 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5448,
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  b';
                                                FStar_Syntax_Syntax.pos =
                                                  uu____5450;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____5451;_})
                                             ->
                                             let uu____5456 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname in
                                             Prims.op_Negation uu____5456
                                         | uu____5458 -> true) subst in
                                  b_for_x :: subst1))
                  | uu____5460 -> subst)) env1 []
let reduce_primops :
  'uuuuuu5482 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5482)
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
            (let uu____5534 = FStar_Syntax_Util.head_and_args tm in
             match uu____5534 with
             | (head, args) ->
                 let uu____5579 =
                   let uu____5580 = FStar_Syntax_Util.un_uinst head in
                   uu____5580.FStar_Syntax_Syntax.n in
                 (match uu____5579 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5586 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                      (match uu____5586 with
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
                                (fun uu____5609 ->
                                   let uu____5610 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name in
                                   let uu____5612 =
                                     FStar_Util.string_of_int l in
                                   let uu____5614 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5610 uu____5612 uu____5614);
                              tm)
                           else
                             (let uu____5619 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args in
                              match uu____5619 with
                              | (args_1, args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5705 ->
                                        let uu____5706 =
                                          FStar_Syntax_Print.term_to_string
                                            tm in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5706);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5711 ->
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
                                           (fun uu____5725 ->
                                              let uu____5726 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5726);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5734 ->
                                              let uu____5735 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              let uu____5737 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5735 uu____5737);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5740 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5744 ->
                                 let uu____5745 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5745);
                            tm)
                       | FStar_Pervasives_Native.None -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5751 ->
                            let uu____5752 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5752);
                       (match args with
                        | (a1, uu____5758)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5783 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5797 ->
                            let uu____5798 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5798);
                       (match args with
                        | (t, uu____5804)::(r, uu____5806)::[] ->
                            let uu____5847 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r in
                            (match uu____5847 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None -> tm)
                        | uu____5853 -> tm))
                  | uu____5864 -> tm))
let reduce_equality :
  'uuuuuu5875 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5875)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb ->
    fun cfg ->
      fun tm ->
        reduce_primops norm_cb
          (let uu___757_5924 = cfg in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___759_5927 = FStar_TypeChecker_Cfg.default_steps in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___759_5927.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___759_5927.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___759_5927.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___759_5927.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___759_5927.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___759_5927.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___759_5927.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___759_5927.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___759_5927.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___759_5927.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___759_5927.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___759_5927.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___759_5927.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___759_5927.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___759_5927.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___759_5927.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___759_5927.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___759_5927.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___759_5927.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___759_5927.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___759_5927.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___759_5927.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___759_5927.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___759_5927.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___759_5927.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___759_5927.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___757_5924.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___757_5924.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___757_5924.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___757_5924.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___757_5924.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___757_5924.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___757_5924.FStar_TypeChecker_Cfg.reifying)
           }) tm
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_none -> true | uu____5938 -> false
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_ready -> true | uu____5949 -> false
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Norm_request_requires_rejig -> true
    | uu____5960 -> false
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd ->
    fun args ->
      let aux min_args =
        let uu____5981 = FStar_All.pipe_right args FStar_List.length in
        FStar_All.pipe_right uu____5981
          (fun n ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig) in
      let uu____6013 =
        let uu____6014 = FStar_Syntax_Util.un_uinst hd in
        uu____6014.FStar_Syntax_Syntax.n in
      match uu____6013 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____6023 -> Norm_request_none
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6032 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid in
       Prims.op_Negation uu____6032)
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd ->
    fun args ->
      let uu____6045 =
        let uu____6046 = FStar_Syntax_Util.un_uinst hd in
        uu____6046.FStar_Syntax_Syntax.n in
      match uu____6045 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6104 = FStar_Syntax_Util.mk_app hd [t1; t2] in
               FStar_Syntax_Util.mk_app uu____6104 rest
           | uu____6131 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6171 = FStar_Syntax_Util.mk_app hd [t] in
               FStar_Syntax_Util.mk_app uu____6171 rest
           | uu____6190 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6264 = FStar_Syntax_Util.mk_app hd [t1; t2; t3] in
               FStar_Syntax_Util.mk_app uu____6264 rest
           | uu____6299 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6301 ->
          let uu____6302 =
            let uu____6304 = FStar_Syntax_Print.term_to_string hd in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6304 in
          failwith uu____6302
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6325 ->
    match uu___9_6325 with
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
        let uu____6332 =
          let uu____6335 =
            let uu____6336 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldOnly uu____6336 in
          [uu____6335] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6332
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____6344 =
          let uu____6347 =
            let uu____6348 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldFully uu____6348 in
          [uu____6347] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6344
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____6356 =
          let uu____6359 =
            let uu____6360 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldAttr uu____6360 in
          [uu____6359] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6356
    | FStar_Syntax_Embeddings.NBE -> [FStar_TypeChecker_Env.NBE]
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s ->
    let s1 = FStar_List.concatMap tr_norm_step s in
    let add_exclude s2 z =
      let uu____6396 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2 in
      if uu____6396 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2 in
    let s2 = FStar_TypeChecker_Env.Beta :: s1 in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota in s4
let get_norm_request :
  'uuuuuu6421 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu6421) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun full_norm ->
      fun args ->
        let parse_steps s =
          let uu____6472 =
            let uu____6477 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6477 s in
          match uu____6472 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6493 = tr_norm_steps steps in
              FStar_Pervasives_Native.Some uu____6493
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
        | uu____6528::(tm, uu____6530)::[] ->
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
        | (tm, uu____6559)::[] ->
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
        | (steps, uu____6580)::uu____6581::(tm, uu____6583)::[] ->
            let uu____6604 =
              let uu____6609 = full_norm steps in parse_steps uu____6609 in
            (match uu____6604 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6639 -> FStar_Pervasives_Native.None
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun s ->
      fun tm ->
        let delta_level =
          let uu____6671 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6678 ->
                    match uu___10_6678 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6680 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6682 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6686 -> true
                    | uu____6690 -> false)) in
          if uu____6671
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta] in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6700 ->
             let uu____6701 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6701);
        (let tm_norm =
           let uu____6705 =
             let uu____6720 = FStar_TypeChecker_Cfg.cfg_env cfg in
             uu____6720.FStar_TypeChecker_Env.nbe in
           uu____6705 s cfg.FStar_TypeChecker_Cfg.tcenv tm in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6724 ->
              let uu____6725 = FStar_Syntax_Print.term_to_string tm_norm in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6725);
         tm_norm)
let firstn :
  'uuuuuu6735 .
    Prims.int ->
      'uuuuuu6735 Prims.list ->
        ('uuuuuu6735 Prims.list * 'uuuuuu6735 Prims.list)
  =
  fun k ->
    fun l ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg ->
    fun stack1 ->
      let rec drop_irrel uu___11_6792 =
        match uu___11_6792 with
        | (MemoLazy uu____6797)::s -> drop_irrel s
        | (UnivArgs uu____6807)::s -> drop_irrel s
        | s -> s in
      let uu____6820 = drop_irrel stack1 in
      match uu____6820 with
      | (App
          (uu____6824,
           {
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify);
             FStar_Syntax_Syntax.pos = uu____6825;
             FStar_Syntax_Syntax.vars = uu____6826;_},
           uu____6827, uu____6828))::uu____6829
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6834 -> false
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t, uu____6863) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t, uu____6873) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6894 ->
                  match uu____6894 with
                  | (a, uu____6905) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args) in
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6916 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6933 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6935 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6949 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6951 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6953 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6955 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6957 -> false
    | FStar_Syntax_Syntax.Tm_unknown -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6960 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6968 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6976 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6991 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7011 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7027 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7035 -> true
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7107 ->
                   match uu____7107 with
                   | (a, uu____7118) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____7129) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7228, args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7283 ->
                        match uu____7283 with
                        | (a, uu____7294) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7303, uu____7304, t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7310, t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7316 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7326 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7328 -> false))
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_no -> true | uu____7339 -> false
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_yes -> true | uu____7350 -> false
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_fully -> true | uu____7361 -> false
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_reify -> true | uu____7372 -> false
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
            let uu____7405 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
            match uu____7405 with
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
              (fun uu____7604 ->
                 fun uu____7605 ->
                   match (uu____7604, uu____7605) with
                   | ((a, b, c), (x, y, z)) -> ((a || x), (b || y), (c || z)))
              l (false, false, false) in
          let string_of_res uu____7711 =
            match uu____7711 with
            | (x, y, z) ->
                let uu____7731 = FStar_Util.string_of_bool x in
                let uu____7733 = FStar_Util.string_of_bool y in
                let uu____7735 = FStar_Util.string_of_bool z in
                FStar_Util.format3 "(%s,%s,%s)" uu____7731 uu____7733
                  uu____7735 in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7763 ->
                    let uu____7764 = FStar_Syntax_Print.fv_to_string fv in
                    let uu____7766 = FStar_Util.string_of_bool b in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7764 uu____7766);
               if b then reif else no)
            else
              if
                (let uu____7781 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                 FStar_Option.isSome uu____7781)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7786 ->
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
                          ((is_rec, uu____7821), uu____7822);
                        FStar_Syntax_Syntax.sigrng = uu____7823;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7825;
                        FStar_Syntax_Syntax.sigattrs = uu____7826;
                        FStar_Syntax_Syntax.sigopts = uu____7827;_},
                      uu____7828),
                     uu____7829),
                    uu____7830, uu____7831, uu____7832) when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7941 ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7943, uu____7944, uu____7945, uu____7946) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8013 ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec, uu____8016), uu____8017);
                        FStar_Syntax_Syntax.sigrng = uu____8018;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8020;
                        FStar_Syntax_Syntax.sigattrs = uu____8021;
                        FStar_Syntax_Syntax.sigopts = uu____8022;_},
                      uu____8023),
                     uu____8024),
                    uu____8025, uu____8026, uu____8027) when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8136 ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8138, FStar_Pervasives_Native.Some uu____8139,
                    uu____8140, uu____8141) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8209 ->
                           let uu____8210 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8210);
                      (let uu____8213 =
                         let uu____8225 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8251 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____8251 in
                         let uu____8263 =
                           let uu____8275 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8301 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8301 in
                           let uu____8317 =
                             let uu____8329 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8355 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8355 in
                             [uu____8329] in
                           uu____8275 :: uu____8317 in
                         uu____8225 :: uu____8263 in
                       comb_or uu____8213))
                 | (uu____8403, uu____8404, FStar_Pervasives_Native.Some
                    uu____8405, uu____8406) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8474 ->
                           let uu____8475 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8475);
                      (let uu____8478 =
                         let uu____8490 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8516 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____8516 in
                         let uu____8528 =
                           let uu____8540 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8566 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8566 in
                           let uu____8582 =
                             let uu____8594 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8620 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8620 in
                             [uu____8594] in
                           uu____8540 :: uu____8582 in
                         uu____8490 :: uu____8528 in
                       comb_or uu____8478))
                 | (uu____8668, uu____8669, uu____8670,
                    FStar_Pervasives_Native.Some uu____8671) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8739 ->
                           let uu____8740 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8740);
                      (let uu____8743 =
                         let uu____8755 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8781 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____8781 in
                         let uu____8793 =
                           let uu____8805 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8831 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8831 in
                           let uu____8847 =
                             let uu____8859 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8885 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8885 in
                             [uu____8859] in
                           uu____8805 :: uu____8847 in
                         uu____8755 :: uu____8793 in
                       comb_or uu____8743))
                 | uu____8933 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8979 ->
                           let uu____8980 =
                             FStar_Syntax_Print.fv_to_string fv in
                           let uu____8982 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta in
                           let uu____8984 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8980 uu____8982 uu____8984);
                      (let uu____8987 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_8993 ->
                                 match uu___12_8993 with
                                 | FStar_TypeChecker_Env.NoDelta -> false
                                 | FStar_TypeChecker_Env.InliningDelta ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                     -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8999 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8999 l)) in
                       FStar_All.pipe_left yesno uu____8987))) in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9015 ->
               let uu____9016 = FStar_Syntax_Print.fv_to_string fv in
               let uu____9018 =
                 let uu____9020 = FStar_Syntax_Syntax.range_of_fv fv in
                 FStar_Range.string_of_range uu____9020 in
               let uu____9021 = string_of_res res in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9016 uu____9018 uu____9021);
          (match res with
           | (false, uu____9024, uu____9025) -> Should_unfold_no
           | (true, false, false) -> Should_unfold_yes
           | (true, true, false) -> Should_unfold_fully
           | (true, false, true) -> Should_unfold_reify
           | uu____9050 ->
               let uu____9060 =
                 let uu____9062 = string_of_res res in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9062 in
               FStar_All.pipe_left failwith uu____9060)
let decide_unfolding :
  'uuuuuu9081 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu9081 ->
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
                    let uu___1168_9150 = cfg in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1170_9153 = cfg.FStar_TypeChecker_Cfg.steps in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1170_9153.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1170_9153.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1168_9150.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9215 = push e t in (UnivArgs (us, r)) ::
                          uu____9215
                    | h::t -> e :: h :: t in
                  let ref =
                    let uu____9227 =
                      let uu____9228 =
                        let uu____9229 = FStar_Syntax_Syntax.lid_of_fv fv in
                        FStar_Const.Const_reflect uu____9229 in
                      FStar_Syntax_Syntax.Tm_constant uu____9228 in
                    FStar_Syntax_Syntax.mk uu____9227 FStar_Range.dummyRange in
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
    let uu____9295 =
      let uu____9296 = FStar_Syntax_Subst.compress t in
      uu____9296.FStar_Syntax_Syntax.n in
    match uu____9295 with
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu____9327 =
          let uu____9328 = FStar_Syntax_Util.un_uinst hd in
          uu____9328.FStar_Syntax_Syntax.n in
        (match uu____9327 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9345 =
                 let uu____9352 =
                   let uu____9363 = FStar_All.pipe_right args FStar_List.tl in
                   FStar_All.pipe_right uu____9363 FStar_List.tl in
                 FStar_All.pipe_right uu____9352 FStar_List.hd in
               FStar_All.pipe_right uu____9345 FStar_Pervasives_Native.fst in
             FStar_Pervasives_Native.Some f
         | uu____9462 -> FStar_Pervasives_Native.None)
    | uu____9463 -> FStar_Pervasives_Native.None
let (is_partial_primop_app :
  FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun cfg ->
    fun t ->
      let uu____9477 = FStar_Syntax_Util.head_and_args t in
      match uu____9477 with
      | (hd, args) ->
          let uu____9521 =
            let uu____9522 = FStar_Syntax_Util.un_uinst hd in
            uu____9522.FStar_Syntax_Syntax.n in
          (match uu____9521 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____9527 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
               (match uu____9527 with
                | FStar_Pervasives_Native.Some prim_step ->
                    prim_step.FStar_TypeChecker_Cfg.arity >
                      (FStar_List.length args)
                | FStar_Pervasives_Native.None -> false)
           | uu____9541 -> false)
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9821 ->
                   let uu____9836 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9836
               | uu____9839 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9849 ->
               let uu____9850 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____9852 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm in
               let uu____9854 = FStar_Syntax_Print.term_to_string t1 in
               let uu____9856 =
                 FStar_Util.string_of_int (FStar_List.length env1) in
               let uu____9864 =
                 let uu____9866 =
                   let uu____9869 = firstn (Prims.of_int (4)) stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9869 in
                 stack_to_string uu____9866 in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9850 uu____9852 uu____9854 uu____9856 uu____9864);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9897 ->
               let uu____9898 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9898);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9904 ->
                     let uu____9905 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9905);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9908 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9912 ->
                     let uu____9913 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9913);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____9916 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9920 ->
                     let uu____9921 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9921);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9924 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9928 ->
                     let uu____9929 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9929);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9932;
                 FStar_Syntax_Syntax.fv_delta = uu____9933;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9937 ->
                     let uu____9938 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9938);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9941;
                 FStar_Syntax_Syntax.fv_delta = uu____9942;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9943);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9953 ->
                     let uu____9954 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9954);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid in
               let uu____9960 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo in
               (match uu____9960 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____9963)
                    when uu____9963 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9967 ->
                          let uu____9968 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9968);
                     rebuild cfg env1 stack1 t1)
                | uu____9971 ->
                    let uu____9974 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo in
                    (match uu____9974 with
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
               let uu____10013 = closure_as_term cfg env1 t2 in
               rebuild cfg env1 stack1 uu____10013
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10041 = is_norm_request hd args in
                  uu____10041 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10047 = rejig_norm_request hd args in
                 norm cfg env1 stack1 uu____10047))
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10075 = is_norm_request hd args in
                  uu____10075 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1292_10082 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1294_10085 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1294_10085.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1292_10082.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1292_10082.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1292_10082.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1292_10082.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1292_10082.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1292_10082.FStar_TypeChecker_Cfg.reifying)
                   } in
                 let uu____10092 =
                   get_norm_request cfg (norm cfg' env1 []) args in
                 match uu____10092 with
                 | FStar_Pervasives_Native.None ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____10128 ->
                                 fun stack2 ->
                                   match uu____10128 with
                                   | (a, aq) ->
                                       let uu____10140 =
                                         let uu____10141 =
                                           let uu____10148 =
                                             let uu____10149 =
                                               let uu____10181 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None in
                                               (env1, a, uu____10181, false) in
                                             Clos uu____10149 in
                                           (uu____10148, aq,
                                             (t1.FStar_Syntax_Syntax.pos)) in
                                         Arg uu____10141 in
                                       uu____10140 :: stack2) args) in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10249 ->
                            let uu____10250 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10250);
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
                         let uu____10282 =
                           let uu____10284 =
                             let uu____10286 = FStar_Util.time_diff start fin in
                             FStar_Pervasives_Native.snd uu____10286 in
                           FStar_Util.string_of_int uu____10284 in
                         let uu____10293 =
                           FStar_Syntax_Print.term_to_string tm' in
                         let uu____10295 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1 in
                         let uu____10297 =
                           FStar_Syntax_Print.term_to_string tm_norm in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10282 uu____10293 uu____10295 uu____10297)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s, tm) ->
                     let delta_level =
                       let uu____10317 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10324 ->
                                 match uu___13_10324 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10326 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10328 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10332 -> true
                                 | uu____10336 -> false)) in
                       if uu____10317
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta] in
                     let cfg'1 =
                       let uu___1332_10344 = cfg in
                       let uu____10345 =
                         let uu___1334_10346 =
                           FStar_TypeChecker_Cfg.to_fsteps s in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1334_10346.FStar_TypeChecker_Cfg.for_extraction)
                         } in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10345;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1332_10344.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1332_10344.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1332_10344.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1332_10344.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1332_10344.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1332_10344.FStar_TypeChecker_Cfg.reifying)
                       } in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1 in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10354 =
                           let uu____10355 =
                             let uu____10360 = FStar_Util.now () in
                             (tm, uu____10360) in
                           Debug uu____10355 in
                         uu____10354 :: tail
                       else tail in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u in
               let uu____10365 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____10365
           | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____10376 =
                      let uu____10383 =
                        FStar_List.map (norm_universe cfg env1) us in
                      (uu____10383, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____10376 in
                  let stack2 = us1 :: stack1 in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10392 = lookup_bvar env1 x in
               (match uu____10392 with
                | Univ uu____10393 ->
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
                      let uu____10447 = FStar_ST.op_Bang r in
                      (match uu____10447 with
                       | FStar_Pervasives_Native.Some (env3, t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10543 ->
                                 let uu____10544 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____10546 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10544
                                   uu____10546);
                            (let uu____10549 = maybe_weakly_reduced t' in
                             if uu____10549
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____10552 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
               (match stack1 with
                | (UnivArgs uu____10596)::uu____10597 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c, uu____10608, uu____10609))::stack_rest ->
                    (match c with
                     | Univ uu____10613 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____10622 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10652 ->
                                    let uu____10653 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10653);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10689 ->
                                    let uu____10690 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10690);
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
                       (fun uu____10738 ->
                          let uu____10739 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10739);
                     norm cfg env1 stack2 t1)
                | (Match uu____10742)::uu____10743 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10758 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10758 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10794 -> dummy :: env2) env1) in
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
                                          let uu____10838 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10838)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10846 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10846.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10846.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10847 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10853 ->
                                 let uu____10854 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10854);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10869 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10869.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____10873)::uu____10874 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10885 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10885 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10921 -> dummy :: env2) env1) in
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
                                          let uu____10965 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10965)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10973 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10973.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10973.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10974 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10980 ->
                                 let uu____10981 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10981);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10996 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10996.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11000)::uu____11001 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11014 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11014 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11050 -> dummy :: env2) env1) in
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
                                          let uu____11094 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11094)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11102 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11102.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11102.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11103 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11109 ->
                                 let uu____11110 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11110);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11125 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11125.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11129)::uu____11130 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11145 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11145 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11181 -> dummy :: env2) env1) in
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
                                          let uu____11225 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11225)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11233 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11233.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11233.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11234 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11240 ->
                                 let uu____11241 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11241);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11256 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11256.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11260)::uu____11261 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11276 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11276 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11312 -> dummy :: env2) env1) in
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
                                          let uu____11356 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11356)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11364 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11364.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11364.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11365 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11371 ->
                                 let uu____11372 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11372);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11387 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11387.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____11391)::uu____11392 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11407 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11407 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11443 -> dummy :: env2) env1) in
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
                                          let uu____11487 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11487)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11495 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11495.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11495.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11496 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11502 ->
                                 let uu____11503 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11503);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11518 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11518.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11522)::uu____11523 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11542 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11542 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11578 -> dummy :: env2) env1) in
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
                                          let uu____11622 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11622)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11630 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11630.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11630.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11631 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11637 ->
                                 let uu____11638 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11638);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11653 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11653.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11661 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11661 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11697 -> dummy :: env2) env1) in
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
                                          let uu____11741 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11741)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11749 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11749.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11749.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11750 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11756 ->
                                 let uu____11757 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11757);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11772 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11772.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head, args) ->
               let strict_args =
                 let uu____11808 =
                   let uu____11809 = FStar_Syntax_Util.un_uinst head in
                   uu____11809.FStar_Syntax_Syntax.n in
                 match uu____11808 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11818 -> FStar_Pervasives_Native.None in
               (match strict_args with
                | FStar_Pervasives_Native.None ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____11839 ->
                              fun stack2 ->
                                match uu____11839 with
                                | (a, aq) ->
                                    let uu____11851 =
                                      let uu____11852 =
                                        let uu____11859 =
                                          let uu____11860 =
                                            let uu____11892 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu____11892, false) in
                                          Clos uu____11860 in
                                        (uu____11859, aq,
                                          (t1.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____11852 in
                                    uu____11851 :: stack2) args) in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11960 ->
                          let uu____11961 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args) in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11961);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12012 ->
                              match uu____12012 with
                              | (a, i) ->
                                  let uu____12023 = norm cfg env1 [] a in
                                  (uu____12023, i))) in
                    let norm_args_len = FStar_List.length norm_args in
                    let uu____12029 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12044 = FStar_List.nth norm_args i in
                                 match uu____12044 with
                                 | (arg_i, uu____12055) ->
                                     let uu____12056 =
                                       FStar_Syntax_Util.head_and_args arg_i in
                                     (match uu____12056 with
                                      | (head1, uu____12075) ->
                                          let uu____12100 =
                                            let uu____12101 =
                                              FStar_Syntax_Util.un_uinst
                                                head1 in
                                            uu____12101.FStar_Syntax_Syntax.n in
                                          (match uu____12100 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12105 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12108 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12108
                                           | uu____12109 -> false))))) in
                    if uu____12029
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____12126 ->
                                fun stack2 ->
                                  match uu____12126 with
                                  | (a, aq) ->
                                      let uu____12138 =
                                        let uu____12139 =
                                          let uu____12146 =
                                            let uu____12147 =
                                              let uu____12179 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a)) in
                                              (env1, a, uu____12179, false) in
                                            Clos uu____12147 in
                                          (uu____12146, aq,
                                            (t1.FStar_Syntax_Syntax.pos)) in
                                        Arg uu____12139 in
                                      uu____12138 :: stack2) norm_args) in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12261 ->
                            let uu____12262 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12262);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x, uu____12280) when
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
                             ((let uu___1525_12325 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1525_12325.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1525_12325.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2
                  | uu____12326 ->
                      let uu____12341 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 uu____12341)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
                  let uu____12345 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12345 with
                  | (closing, f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1 in
                      let t2 =
                        let uu____12376 =
                          let uu____12377 =
                            let uu____12384 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___1534_12390 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1534_12390.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1534_12390.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12384) in
                          FStar_Syntax_Syntax.Tm_refine uu____12377 in
                        FStar_Syntax_Syntax.mk uu____12376
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12414 = closure_as_term cfg env1 t1 in
                 rebuild cfg env1 stack1 uu____12414
               else
                 (let uu____12417 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12417 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu____12425 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2 -> fun uu____12451 -> dummy :: env2)
                               env1) in
                        norm_comp cfg uu____12425 c1 in
                      let t2 =
                        let uu____12475 = norm_binders cfg env1 bs1 in
                        FStar_Syntax_Util.arrow uu____12475 c2 in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) ->
               (match stack1 with
                | (Match uu____12588)::uu____12589 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12602 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____12604)::uu____12605 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12616 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____12618,
                     {
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify);
                       FStar_Syntax_Syntax.pos = uu____12619;
                       FStar_Syntax_Syntax.vars = uu____12620;_},
                     uu____12621, uu____12622))::uu____12623
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12630 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____12632)::uu____12633 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12644 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____12646 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12649 ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11 in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12654 ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12680 = norm cfg env1 [] t2 in
                             FStar_Util.Inl uu____12680
                         | FStar_Util.Inr c ->
                             let uu____12694 = norm_comp cfg env1 c in
                             FStar_Util.Inr uu____12694 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 []) in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____12717 =
                               let uu____12718 =
                                 let uu____12745 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____12745, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12718 in
                             FStar_Syntax_Syntax.mk uu____12717
                               t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env1 stack2 t2
                       | uu____12780 ->
                           let uu____12781 =
                             let uu____12782 =
                               let uu____12783 =
                                 let uu____12810 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____12810, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12783 in
                             FStar_Syntax_Syntax.mk uu____12782
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env1 stack1 uu____12781))))
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
                   let uu___1613_12888 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1615_12891 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1615_12891.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1613_12888.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12932 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____12932 with
                         | (openings, lbunivs) ->
                             let cfg1 =
                               let uu___1628_12952 = cfg in
                               let uu____12953 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12953;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1628_12952.FStar_TypeChecker_Cfg.reifying)
                               } in
                             let norm1 t2 =
                               let uu____12960 =
                                 let uu____12961 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env1 [] uu____12961 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12960 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___1635_12964 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1635_12964.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1635_12964.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1635_12964.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1635_12964.FStar_Syntax_Syntax.lbpos)
                             })) in
               let uu____12965 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____12965
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12978,
                 { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____12979;
                   FStar_Syntax_Syntax.lbunivs = uu____12980;
                   FStar_Syntax_Syntax.lbtyp = uu____12981;
                   FStar_Syntax_Syntax.lbeff = uu____12982;
                   FStar_Syntax_Syntax.lbdef = uu____12983;
                   FStar_Syntax_Syntax.lbattrs = uu____12984;
                   FStar_Syntax_Syntax.lbpos = uu____12985;_}::uu____12986),
                uu____12987)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
               let uu____13032 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb in
               if uu____13032
               then
                 let binder =
                   let uu____13036 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13036 in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef in
                 let env2 =
                   let uu____13047 =
                     let uu____13054 =
                       let uu____13055 =
                         let uu____13087 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env1, def, uu____13087, false) in
                       Clos uu____13055 in
                     ((FStar_Pervasives_Native.Some binder), uu____13054) in
                   uu____13047 :: env1 in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13162 ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____13166 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13169 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff in
                       FStar_Syntax_Util.is_div_effect uu____13169) in
                  if uu____13166
                  then
                    let ffun =
                      let uu____13174 =
                        let uu____13175 =
                          let uu____13194 =
                            let uu____13203 =
                              let uu____13210 =
                                FStar_All.pipe_right
                                  lb.FStar_Syntax_Syntax.lbname
                                  FStar_Util.left in
                              FStar_Syntax_Syntax.mk_binder uu____13210 in
                            [uu____13203] in
                          (uu____13194, body, FStar_Pervasives_Native.None) in
                        FStar_Syntax_Syntax.Tm_abs uu____13175 in
                      FStar_Syntax_Syntax.mk uu____13174
                        t1.FStar_Syntax_Syntax.pos in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13244 ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13251 ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13253 = closure_as_term cfg env1 t1 in
                        rebuild cfg env1 stack1 uu____13253))
                    else
                      (let uu____13256 =
                         let uu____13261 =
                           let uu____13262 =
                             let uu____13269 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left in
                             FStar_All.pipe_right uu____13269
                               FStar_Syntax_Syntax.mk_binder in
                           [uu____13262] in
                         FStar_Syntax_Subst.open_term uu____13261 body in
                       match uu____13256 with
                       | (bs, body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13296 ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                             let lbname =
                               let x =
                                 let uu____13305 = FStar_List.hd bs in
                                 FStar_Pervasives_Native.fst uu____13305 in
                               FStar_Util.Inl
                                 (let uu___1682_13321 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1682_13321.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1682_13321.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }) in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13324 ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1687_13327 = lb in
                                let uu____13328 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef in
                                let uu____13331 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1687_13327.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1687_13327.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13328;
                                  FStar_Syntax_Syntax.lbattrs = uu____13331;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1687_13327.FStar_Syntax_Syntax.lbpos)
                                } in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2 ->
                                        fun uu____13366 -> dummy :: env2)
                                     env1) in
                              let stack2 = (Cfg cfg) :: stack1 in
                              let cfg1 =
                                let uu___1694_13391 = cfg in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1694_13391.FStar_TypeChecker_Cfg.reifying)
                                } in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13395 ->
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
               let uu____13416 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13416 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13452 =
                               let uu___1710_13453 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1710_13453.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1710_13453.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13452 in
                           let uu____13454 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13454 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env1 xs in
                               let env2 =
                                 let uu____13480 =
                                   FStar_List.map (fun uu____13502 -> dummy)
                                     xs1 in
                                 let uu____13509 =
                                   let uu____13518 =
                                     FStar_List.map
                                       (fun uu____13534 -> dummy) lbs1 in
                                   FStar_List.append uu____13518 env1 in
                                 FStar_List.append uu____13480 uu____13509 in
                               let def_body1 = norm cfg env2 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13554 =
                                       let uu___1724_13555 = rc in
                                       let uu____13556 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1724_13555.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13556;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1724_13555.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13554
                                 | uu____13565 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___1729_13571 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1729_13571.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1729_13571.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1729_13571.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1729_13571.FStar_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu____13581 =
                        FStar_List.map (fun uu____13597 -> dummy) lbs2 in
                      FStar_List.append uu____13581 env1 in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13605 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13605 with
                     | (lbs3, body3) ->
                         let t2 =
                           let uu___1738_13621 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1738_13621.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1738_13621.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs, body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13655 = closure_as_term cfg env1 t1 in
               rebuild cfg env1 stack1 uu____13655
           | FStar_Syntax_Syntax.Tm_let (lbs, body) ->
               let uu____13676 =
                 FStar_List.fold_right
                   (fun lb ->
                      fun uu____13754 ->
                        match uu____13754 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___1754_13879 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1754_13879.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1754_13879.FStar_Syntax_Syntax.sort)
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
               (match uu____13676 with
                | (rec_env, memos, uu____14070) ->
                    let uu____14125 =
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
                             let uu____14374 =
                               let uu____14381 =
                                 let uu____14382 =
                                   let uu____14414 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14414, false) in
                                 Clos uu____14382 in
                               (FStar_Pervasives_Native.None, uu____14381) in
                             uu____14374 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1 in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head, m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14499 ->
                     let uu____14500 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14500);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1, t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14524 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____14528::uu____14529 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l, r, uu____14534) ->
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
                             | uu____14613 -> norm cfg env1 stack1 head)
                        | [] ->
                            let head1 = norm cfg env1 [] head in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names, args) ->
                                  let names1 =
                                    FStar_All.pipe_right names
                                      (FStar_List.map (norm cfg env1 [])) in
                                  let uu____14661 =
                                    let uu____14682 =
                                      norm_pattern_args cfg env1 args in
                                    (names1, uu____14682) in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14661
                              | uu____14711 -> m in
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14717 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14733 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14747 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14761 =
                        let uu____14763 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____14765 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14763 uu____14765 in
                      failwith uu____14761
                    else
                      (let uu____14770 = inline_closure_env cfg env1 [] t2 in
                       rebuild cfg env1 stack1 uu____14770)
                | uu____14771 -> norm cfg env1 stack1 t2))
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
              let uu____14780 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu____14780 with
              | FStar_Pervasives_Native.None ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14794 ->
                        let uu____14795 = FStar_Syntax_Print.fv_to_string f in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14795);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us, t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14808 ->
                        let uu____14809 =
                          FStar_Syntax_Print.term_to_string t0 in
                        let uu____14811 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14809 uu____14811);
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
                      | (UnivArgs (us', uu____14824))::stack2 ->
                          ((let uu____14833 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm") in
                            if uu____14833
                            then
                              FStar_List.iter
                                (fun x ->
                                   let uu____14841 =
                                     FStar_Syntax_Print.univ_to_string x in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14841) us'
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
                      | uu____14877 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____14880 ->
                          let uu____14883 =
                            let uu____14885 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14885 in
                          failwith uu____14883
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
              let uu____14905 =
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
                    let uu___1865_14923 = cfg in
                    let uu____14924 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____14924;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1865_14923.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1865_14923.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1865_14923.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1865_14923.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1865_14923.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1865_14923.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1865_14923.FStar_TypeChecker_Cfg.reifying)
                    } in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1) in
              match uu____14905 with
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
                     (uu____14965,
                      {
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify);
                        FStar_Syntax_Syntax.pos = uu____14966;
                        FStar_Syntax_Syntax.vars = uu____14967;_},
                      uu____14968, uu____14969))::uu____14970
                     -> ()
                 | uu____14975 ->
                     let uu____14978 =
                       let uu____14980 = stack_to_string stack1 in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14980 in
                     failwith uu____14978);
                (let top0 = top in
                 let top1 = FStar_Syntax_Util.unascribe top in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14989 ->
                      let uu____14990 = FStar_Syntax_Print.tag_of_term top1 in
                      let uu____14992 =
                        FStar_Syntax_Print.term_to_string top1 in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14990
                        uu____14992);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1 in
                  let uu____14996 =
                    let uu____14997 = FStar_Syntax_Subst.compress top2 in
                    uu____14997.FStar_Syntax_Syntax.n in
                  match uu____14996 with
                  | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name in
                      let uu____15019 =
                        let uu____15028 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr in
                        FStar_All.pipe_right uu____15028 FStar_Util.must in
                      (match uu____15019 with
                       | (uu____15043, repr) ->
                           let uu____15053 =
                             let uu____15060 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr in
                             FStar_All.pipe_right uu____15060 FStar_Util.must in
                           (match uu____15053 with
                            | (uu____15097, bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15103 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15114 =
                                         let uu____15115 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15115.FStar_Syntax_Syntax.n in
                                       match uu____15114 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,
                                            FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15121, uu____15122))
                                           ->
                                           let uu____15131 =
                                             let uu____15132 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15132.FStar_Syntax_Syntax.n in
                                           (match uu____15131 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,
                                                 FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15138, msrc,
                                                  uu____15140))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15149 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15149
                                            | uu____15150 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15151 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15152 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15152 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1944_15157 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1944_15157.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1944_15157.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1944_15157.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1944_15157.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1944_15157.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let uu____15158 =
                                            FStar_List.tl stack1 in
                                          let uu____15159 =
                                            let uu____15160 =
                                              let uu____15161 =
                                                let uu____15175 =
                                                  FStar_Syntax_Util.mk_reify
                                                    body in
                                                ((false, [lb1]), uu____15175) in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu____15161 in
                                            FStar_Syntax_Syntax.mk
                                              uu____15160
                                              top2.FStar_Syntax_Syntax.pos in
                                          norm cfg env1 uu____15158
                                            uu____15159
                                      | FStar_Pervasives_Native.None ->
                                          let uu____15191 =
                                            let uu____15193 = is_return body in
                                            match uu____15193 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15198;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15199;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15202 -> false in
                                          if uu____15191
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
                                               let uu____15230 =
                                                 let uu____15231 =
                                                   let uu____15250 =
                                                     let uu____15259 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         x in
                                                     [uu____15259] in
                                                   (uu____15250, body1,
                                                     (FStar_Pervasives_Native.Some
                                                        body_rc)) in
                                                 FStar_Syntax_Syntax.Tm_abs
                                                   uu____15231 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15230
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close =
                                               closure_as_term cfg env1 in
                                             let bind_inst =
                                               let uu____15298 =
                                                 let uu____15299 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15299.FStar_Syntax_Syntax.n in
                                               match uu____15298 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind,
                                                    uu____15305::uu____15306::[])
                                                   ->
                                                   let uu____15311 =
                                                     let uu____15312 =
                                                       let uu____15319 =
                                                         let uu____15320 =
                                                           let uu____15321 =
                                                             close
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.FStar_TypeChecker_Cfg.tcenv
                                                             uu____15321 in
                                                         let uu____15322 =
                                                           let uu____15325 =
                                                             let uu____15326
                                                               = close t in
                                                             (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.FStar_TypeChecker_Cfg.tcenv
                                                               uu____15326 in
                                                           [uu____15325] in
                                                         uu____15320 ::
                                                           uu____15322 in
                                                       (bind, uu____15319) in
                                                     FStar_Syntax_Syntax.Tm_uinst
                                                       uu____15312 in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____15311 rng
                                               | uu____15329 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let bind_inst_args f_arg =
                                               let uu____15341 =
                                                 FStar_Syntax_Util.is_layered
                                                   ed in
                                               if uu____15341
                                               then
                                                 let unit_args =
                                                   let uu____15349 =
                                                     let uu____15350 =
                                                       let uu____15353 =
                                                         let uu____15354 =
                                                           FStar_All.pipe_right
                                                             ed
                                                             FStar_Syntax_Util.get_bind_vc_combinator in
                                                         FStar_All.pipe_right
                                                           uu____15354
                                                           FStar_Pervasives_Native.snd in
                                                       FStar_All.pipe_right
                                                         uu____15353
                                                         FStar_Syntax_Subst.compress in
                                                     uu____15350.FStar_Syntax_Syntax.n in
                                                   match uu____15349 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (uu____15387::uu____15388::bs,
                                                        uu____15390)
                                                       when
                                                       (FStar_List.length bs)
                                                         >=
                                                         (Prims.of_int (2))
                                                       ->
                                                       let uu____15442 =
                                                         let uu____15451 =
                                                           FStar_All.pipe_right
                                                             bs
                                                             (FStar_List.splitAt
                                                                ((FStar_List.length
                                                                    bs)
                                                                   -
                                                                   (Prims.of_int (2)))) in
                                                         FStar_All.pipe_right
                                                           uu____15451
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____15442
                                                         (FStar_List.map
                                                            (fun uu____15574
                                                               ->
                                                               FStar_Syntax_Syntax.as_arg
                                                                 FStar_Syntax_Syntax.unit_const))
                                                   | uu____15581 ->
                                                       let uu____15582 =
                                                         let uu____15588 =
                                                           let uu____15590 =
                                                             FStar_Ident.string_of_lid
                                                               ed.FStar_Syntax_Syntax.mname in
                                                           let uu____15592 =
                                                             let uu____15594
                                                               =
                                                               let uu____15595
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator in
                                                               FStar_All.pipe_right
                                                                 uu____15595
                                                                 FStar_Pervasives_Native.snd in
                                                             FStar_All.pipe_right
                                                               uu____15594
                                                               FStar_Syntax_Print.term_to_string in
                                                           FStar_Util.format2
                                                             "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                             uu____15590
                                                             uu____15592 in
                                                         (FStar_Errors.Fatal_UnexpectedEffect,
                                                           uu____15588) in
                                                       FStar_Errors.raise_error
                                                         uu____15582 rng in
                                                 let uu____15621 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15622 =
                                                   let uu____15625 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15626 =
                                                     let uu____15629 =
                                                       let uu____15632 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           f_arg in
                                                       let uu____15633 =
                                                         let uu____15636 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2 in
                                                         [uu____15636] in
                                                       uu____15632 ::
                                                         uu____15633 in
                                                     FStar_List.append
                                                       unit_args uu____15629 in
                                                   uu____15625 :: uu____15626 in
                                                 uu____15621 :: uu____15622
                                               else
                                                 (let maybe_range_arg =
                                                    let uu____15642 =
                                                      FStar_Util.for_some
                                                        (FStar_Syntax_Util.attr_eq
                                                           FStar_Syntax_Util.dm4f_bind_range_attr)
                                                        ed.FStar_Syntax_Syntax.eff_attrs in
                                                    if uu____15642
                                                    then
                                                      let uu____15647 =
                                                        let uu____15648 =
                                                          FStar_TypeChecker_Cfg.embed_simple
                                                            FStar_Syntax_Embeddings.e_range
                                                            lb.FStar_Syntax_Syntax.lbpos
                                                            lb.FStar_Syntax_Syntax.lbpos in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____15648 in
                                                      let uu____15649 =
                                                        let uu____15652 =
                                                          let uu____15653 =
                                                            FStar_TypeChecker_Cfg.embed_simple
                                                              FStar_Syntax_Embeddings.e_range
                                                              body2.FStar_Syntax_Syntax.pos
                                                              body2.FStar_Syntax_Syntax.pos in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu____15653 in
                                                        [uu____15652] in
                                                      uu____15647 ::
                                                        uu____15649
                                                    else [] in
                                                  let uu____15656 =
                                                    let uu____15659 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp in
                                                    let uu____15660 =
                                                      let uu____15663 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t in
                                                      [uu____15663] in
                                                    uu____15659 ::
                                                      uu____15660 in
                                                  let uu____15664 =
                                                    let uu____15667 =
                                                      let uu____15670 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun in
                                                      let uu____15671 =
                                                        let uu____15674 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            f_arg in
                                                        let uu____15675 =
                                                          let uu____15678 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu____15679 =
                                                            let uu____15682 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2 in
                                                            [uu____15682] in
                                                          uu____15678 ::
                                                            uu____15679 in
                                                        uu____15674 ::
                                                          uu____15675 in
                                                      uu____15670 ::
                                                        uu____15671 in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____15667 in
                                                  FStar_List.append
                                                    uu____15656 uu____15664) in
                                             let reified =
                                               let is_total_effect =
                                                 FStar_TypeChecker_Env.is_total_effect
                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                   eff_name in
                                               if is_total_effect
                                               then
                                                 let uu____15687 =
                                                   let uu____15688 =
                                                     let uu____15705 =
                                                       bind_inst_args head in
                                                     (bind_inst, uu____15705) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15688 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15687 rng
                                               else
                                                 (let uu____15730 =
                                                    let bv =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        x.FStar_Syntax_Syntax.sort in
                                                    let lb1 =
                                                      let uu____15739 =
                                                        let uu____15742 =
                                                          let uu____15753 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              x.FStar_Syntax_Syntax.sort in
                                                          [uu____15753] in
                                                        FStar_Syntax_Util.mk_app
                                                          repr uu____15742 in
                                                      {
                                                        FStar_Syntax_Syntax.lbname
                                                          =
                                                          (FStar_Util.Inl bv);
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = [];
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____15739;
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
                                                    let uu____15783 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        bv in
                                                    (lb1, bv, uu____15783) in
                                                  match uu____15730 with
                                                  | (lb_head, head_bv, head1)
                                                      ->
                                                      let uu____15787 =
                                                        let uu____15788 =
                                                          let uu____15802 =
                                                            let uu____15805 =
                                                              let uu____15812
                                                                =
                                                                let uu____15813
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    head_bv in
                                                                [uu____15813] in
                                                              FStar_Syntax_Subst.close
                                                                uu____15812 in
                                                            let uu____15832 =
                                                              let uu____15833
                                                                =
                                                                let uu____15834
                                                                  =
                                                                  let uu____15851
                                                                    =
                                                                    bind_inst_args
                                                                    head1 in
                                                                  (bind_inst,
                                                                    uu____15851) in
                                                                FStar_Syntax_Syntax.Tm_app
                                                                  uu____15834 in
                                                              FStar_Syntax_Syntax.mk
                                                                uu____15833
                                                                rng in
                                                            FStar_All.pipe_left
                                                              uu____15805
                                                              uu____15832 in
                                                          ((false, [lb_head]),
                                                            uu____15802) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____15788 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____15787 rng) in
                                             FStar_TypeChecker_Cfg.log cfg
                                               (fun uu____15893 ->
                                                  let uu____15894 =
                                                    FStar_Syntax_Print.term_to_string
                                                      top0 in
                                                  let uu____15896 =
                                                    FStar_Syntax_Print.term_to_string
                                                      reified in
                                                  FStar_Util.print2
                                                    "Reified (1) <%s> to %s\n"
                                                    uu____15894 uu____15896);
                                             (let uu____15899 =
                                                FStar_List.tl stack1 in
                                              norm cfg env1 uu____15899
                                                reified))))))
                  | FStar_Syntax_Syntax.Tm_app (head, args) ->
                      ((let uu____15927 = FStar_Options.defensive () in
                        if uu____15927
                        then
                          let is_arg_impure uu____15942 =
                            match uu____15942 with
                            | (e, q) ->
                                let uu____15956 =
                                  let uu____15957 =
                                    FStar_Syntax_Subst.compress e in
                                  uu____15957.FStar_Syntax_Syntax.n in
                                (match uu____15956 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,
                                      FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1, m2, t'))
                                     ->
                                     let uu____15973 =
                                       FStar_Syntax_Util.is_pure_effect m1 in
                                     Prims.op_Negation uu____15973
                                 | uu____15975 -> false) in
                          let uu____15977 =
                            let uu____15979 =
                              let uu____15990 =
                                FStar_Syntax_Syntax.as_arg head in
                              uu____15990 :: args in
                            FStar_Util.for_some is_arg_impure uu____15979 in
                          (if uu____15977
                           then
                             let uu____16016 =
                               let uu____16022 =
                                 let uu____16024 =
                                   FStar_Syntax_Print.term_to_string top2 in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16024 in
                               (FStar_Errors.Warning_Defensive, uu____16022) in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16016
                           else ())
                        else ());
                       (let fallback1 uu____16037 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16041 ->
                               let uu____16042 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16042 "");
                          (let uu____16046 = FStar_List.tl stack1 in
                           let uu____16047 = FStar_Syntax_Util.mk_reify top2 in
                           norm cfg env1 uu____16046 uu____16047) in
                        let fallback2 uu____16053 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16057 ->
                               let uu____16058 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16058 "");
                          (let uu____16062 = FStar_List.tl stack1 in
                           let uu____16063 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos in
                           norm cfg env1 uu____16062 uu____16063) in
                        let uu____16068 =
                          let uu____16069 = FStar_Syntax_Util.un_uinst head in
                          uu____16069.FStar_Syntax_Syntax.n in
                        match uu____16068 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid in
                            let uu____16075 =
                              let uu____16077 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid in
                              Prims.op_Negation uu____16077 in
                            if uu____16075
                            then fallback1 ()
                            else
                              (let uu____16082 =
                                 let uu____16084 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isNone uu____16084 in
                               if uu____16082
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16099 =
                                      FStar_Syntax_Util.mk_reify head in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____16099
                                      args t.FStar_Syntax_Syntax.pos in
                                  let uu____16100 = FStar_List.tl stack1 in
                                  norm cfg env1 uu____16100 t1))
                        | uu____16101 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic uu____16103) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, t'))
                      ->
                      let lifted =
                        let uu____16127 = closure_as_term cfg env1 t' in
                        reify_lift cfg e msrc mtgt uu____16127 in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16131 ->
                            let uu____16132 =
                              FStar_Syntax_Print.term_to_string lifted in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16132);
                       (let uu____16135 = FStar_List.tl stack1 in
                        norm cfg env1 uu____16135 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e, branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____16256 ->
                                match uu____16256 with
                                | (pat, wopt, tm) ->
                                    let uu____16304 =
                                      FStar_Syntax_Util.mk_reify tm in
                                    (pat, wopt, uu____16304))) in
                      let tm =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos in
                      let uu____16336 = FStar_List.tl stack1 in
                      norm cfg env1 uu____16336 tm
                  | uu____16337 -> fallback ()))
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
              (fun uu____16351 ->
                 let uu____16352 = FStar_Ident.string_of_lid msrc in
                 let uu____16354 = FStar_Ident.string_of_lid mtgt in
                 let uu____16356 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16352
                   uu____16354 uu____16356);
            (let uu____16359 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16362 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1) in
                  Prims.op_Negation uu____16362) in
             if uu____16359
             then
               let ed =
                 let uu____16367 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____16367 in
               let uu____16368 =
                 let uu____16377 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 FStar_All.pipe_right uu____16377 FStar_Util.must in
               match uu____16368 with
               | (uu____16424, repr) ->
                   let uu____16434 =
                     let uu____16443 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr in
                     FStar_All.pipe_right uu____16443 FStar_Util.must in
                   (match uu____16434 with
                    | (uu____16490, return_repr) ->
                        let return_inst =
                          let uu____16503 =
                            let uu____16504 =
                              FStar_Syntax_Subst.compress return_repr in
                            uu____16504.FStar_Syntax_Syntax.n in
                          match uu____16503 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm, uu____16510::[]) ->
                              let uu____16515 =
                                let uu____16516 =
                                  let uu____16523 =
                                    let uu____16524 =
                                      env1.FStar_TypeChecker_Env.universe_of
                                        env1 t in
                                    [uu____16524] in
                                  (return_tm, uu____16523) in
                                FStar_Syntax_Syntax.Tm_uinst uu____16516 in
                              FStar_Syntax_Syntax.mk uu____16515
                                e.FStar_Syntax_Syntax.pos
                          | uu____16527 ->
                              failwith "NIY : Reification of indexed effects" in
                        let uu____16531 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t in
                          let lb =
                            let uu____16542 =
                              let uu____16545 =
                                let uu____16556 =
                                  FStar_Syntax_Syntax.as_arg t in
                                [uu____16556] in
                              FStar_Syntax_Util.mk_app repr uu____16545 in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____16542;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            } in
                          let uu____16583 = FStar_Syntax_Syntax.bv_to_name bv in
                          (lb, bv, uu____16583) in
                        (match uu____16531 with
                         | (lb_e, e_bv, e1) ->
                             let uu____16595 =
                               let uu____16596 =
                                 let uu____16610 =
                                   let uu____16613 =
                                     let uu____16620 =
                                       let uu____16621 =
                                         FStar_Syntax_Syntax.mk_binder e_bv in
                                       [uu____16621] in
                                     FStar_Syntax_Subst.close uu____16620 in
                                   let uu____16640 =
                                     let uu____16641 =
                                       let uu____16642 =
                                         let uu____16659 =
                                           let uu____16670 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____16679 =
                                             let uu____16690 =
                                               FStar_Syntax_Syntax.as_arg e1 in
                                             [uu____16690] in
                                           uu____16670 :: uu____16679 in
                                         (return_inst, uu____16659) in
                                       FStar_Syntax_Syntax.Tm_app uu____16642 in
                                     FStar_Syntax_Syntax.mk uu____16641
                                       e1.FStar_Syntax_Syntax.pos in
                                   FStar_All.pipe_left uu____16613
                                     uu____16640 in
                                 ((false, [lb_e]), uu____16610) in
                               FStar_Syntax_Syntax.Tm_let uu____16596 in
                             FStar_Syntax_Syntax.mk uu____16595
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____16752 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt in
                match uu____16752 with
                | FStar_Pervasives_Native.None ->
                    let uu____16755 =
                      let uu____16757 = FStar_Ident.string_of_lid msrc in
                      let uu____16759 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16757 uu____16759 in
                    failwith uu____16755
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16762;
                      FStar_TypeChecker_Env.mtarget = uu____16763;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16764;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None;_};_}
                    ->
                    let uu____16784 =
                      let uu____16786 = FStar_Ident.string_of_lid msrc in
                      let uu____16788 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16786 uu____16788 in
                    failwith uu____16784
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16791;
                      FStar_TypeChecker_Env.mtarget = uu____16792;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16793;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____16824 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc in
                      if uu____16824
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____16829 =
                           let uu____16830 =
                             let uu____16849 =
                               let uu____16858 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_Syntax_Syntax.t_unit in
                               [uu____16858] in
                             (uu____16849, e,
                               (FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      msrc;
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t);
                                    FStar_Syntax_Syntax.residual_flags = []
                                  })) in
                           FStar_Syntax_Syntax.Tm_abs uu____16830 in
                         FStar_Syntax_Syntax.mk uu____16829
                           e.FStar_Syntax_Syntax.pos) in
                    let uu____16891 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t in
                    lift uu____16891 t e1))
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
                (fun uu____16961 ->
                   match uu____16961 with
                   | (a, imp) ->
                       let uu____16980 = norm cfg env1 [] a in
                       (uu____16980, imp))))
and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg ->
    fun env1 ->
      fun comp ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____16990 ->
             let uu____16991 = FStar_Syntax_Print.comp_to_string comp in
             let uu____16993 =
               FStar_Util.string_of_int (FStar_List.length env1) in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____16991 uu____16993);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17019 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____17022 ->
                        FStar_Pervasives_Native.Some uu____17022) uu____17019
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2128_17023 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2128_17023.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2128_17023.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17045 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____17048 ->
                        FStar_Pervasives_Native.Some uu____17048) uu____17045
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2139_17049 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2139_17049.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2139_17049.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let effect_args =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                  then
                    FStar_List.map
                      (fun uu____17113 ->
                         FStar_All.pipe_right FStar_Syntax_Syntax.unit_const
                           FStar_Syntax_Syntax.as_arg)
                  else
                    FStar_List.mapi
                      (fun idx ->
                         fun uu____17140 ->
                           match uu____17140 with
                           | (a, i) ->
                               let uu____17160 = norm cfg env1 [] a in
                               (uu____17160, i))) in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17173 ->
                       match uu___14_17173 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17177 = norm cfg env1 [] t in
                           FStar_Syntax_Syntax.DECREASES uu____17177
                       | f -> f)) in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ in
             let uu___2157_17185 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2159_17188 = ct in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2159_17188.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2157_17185.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2157_17185.FStar_Syntax_Syntax.vars)
             })
and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg ->
    fun env1 ->
      fun b ->
        let uu____17192 = b in
        match uu____17192 with
        | (x, imp) ->
            let x1 =
              let uu___2167_17200 = x in
              let uu____17201 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2167_17200.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2167_17200.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17201
              } in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
                  let uu____17212 =
                    let uu____17213 =
                      let uu____17214 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____17214 in
                    FStar_Syntax_Syntax.Meta uu____17213 in
                  FStar_Pervasives_Native.Some uu____17212
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
                  let uu____17220 =
                    let uu____17221 =
                      let uu____17222 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____17222 in
                    FStar_Syntax_Syntax.Meta uu____17221 in
                  FStar_Pervasives_Native.Some uu____17220
              | i -> i in
            (x1, imp1)
and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu____17233 =
          FStar_List.fold_left
            (fun uu____17267 ->
               fun b ->
                 match uu____17267 with
                 | (nbs', env2) ->
                     let b1 = norm_binder cfg env2 b in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs in
        match uu____17233 with | (nbs, uu____17347) -> FStar_List.rev nbs
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
            let uu____17379 =
              let uu___2197_17380 = rc in
              let uu____17381 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2197_17380.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17381;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2197_17380.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17379
        | uu____17399 -> lopt
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
            (let uu____17409 = FStar_Syntax_Print.term_to_string tm in
             let uu____17411 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17409 uu____17411)
          else ();
          tm'
and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg ->
    fun uu___15_17423 ->
      match uu___15_17423 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17436 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l in
          (match uu____17436 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None ->
               let uu____17440 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None in
               FStar_Syntax_Syntax.fv_to_tm uu____17440)
and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let tm1 =
            let uu____17448 = norm_cb cfg in
            reduce_primops uu____17448 cfg env1 tm in
          let uu____17453 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify in
          if uu____17453
          then tm1
          else
            (let w t =
               let uu___2226_17472 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2226_17472.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2226_17472.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               let uu____17484 =
                 let uu____17485 = FStar_Syntax_Util.unmeta t in
                 uu____17485.FStar_Syntax_Syntax.n in
               match uu____17484 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17497 -> FStar_Pervasives_Native.None in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t, uu____17561)::args1, (bv, uu____17564)::bs1) ->
                   let uu____17618 =
                     let uu____17619 = FStar_Syntax_Subst.compress t in
                     uu____17619.FStar_Syntax_Syntax.n in
                   (match uu____17618 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17624 -> false)
               | ([], []) -> true
               | (uu____17655, uu____17656) -> false in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17707 = FStar_Syntax_Print.term_to_string t in
                  let uu____17709 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17707
                    uu____17709)
               else ();
               (let uu____17714 = FStar_Syntax_Util.head_and_args' t in
                match uu____17714 with
                | (hd, args) ->
                    let uu____17753 =
                      let uu____17754 = FStar_Syntax_Subst.compress hd in
                      uu____17754.FStar_Syntax_Syntax.n in
                    (match uu____17753 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____17762 =
                               FStar_Syntax_Print.term_to_string t in
                             let uu____17764 =
                               FStar_Syntax_Print.bv_to_string bv in
                             let uu____17766 =
                               FStar_Syntax_Print.term_to_string hd in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17762 uu____17764 uu____17766)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17771 -> FStar_Pervasives_Native.None)) in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17789 = FStar_Syntax_Print.term_to_string t in
                  let uu____17791 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17789
                    uu____17791)
               else ();
               (let uu____17796 = FStar_Syntax_Util.is_squash t in
                match uu____17796 with
                | FStar_Pervasives_Native.Some (uu____17807, t') ->
                    is_applied bs t'
                | uu____17819 ->
                    let uu____17828 = FStar_Syntax_Util.is_auto_squash t in
                    (match uu____17828 with
                     | FStar_Pervasives_Native.Some (uu____17839, t') ->
                         is_applied bs t'
                     | uu____17851 -> is_applied bs t)) in
             let is_quantified_const bv phi =
               let uu____17875 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____17875 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid, (p, uu____17882)::(q, uu____17884)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17927 = FStar_Syntax_Print.term_to_string p in
                       let uu____17929 = FStar_Syntax_Print.term_to_string q in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17927 uu____17929)
                    else ();
                    (let uu____17934 =
                       FStar_Syntax_Util.destruct_typ_as_formula p in
                     match uu____17934 with
                     | FStar_Pervasives_Native.None ->
                         let uu____17939 =
                           let uu____17940 = FStar_Syntax_Subst.compress p in
                           uu____17940.FStar_Syntax_Syntax.n in
                         (match uu____17939 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17951 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q in
                                FStar_Pervasives_Native.Some uu____17951))
                          | uu____17954 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1, (p1, uu____17957)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17982 =
                           let uu____17983 = FStar_Syntax_Subst.compress p1 in
                           uu____17983.FStar_Syntax_Syntax.n in
                         (match uu____17982 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17994 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q in
                                FStar_Pervasives_Native.Some uu____17994))
                          | uu____17997 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs, pats, phi1)) ->
                         let uu____18001 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1 in
                         (match uu____18001 with
                          | FStar_Pervasives_Native.None ->
                              let uu____18006 =
                                is_applied_maybe_squashed bs phi1 in
                              (match uu____18006 with
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
                                     let uu____18020 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____18020))
                               | uu____18023 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1, (p1, uu____18028)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18053 =
                                is_applied_maybe_squashed bs p1 in
                              (match uu____18053 with
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
                                     let uu____18067 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____18067))
                               | uu____18070 -> FStar_Pervasives_Native.None)
                          | uu____18073 -> FStar_Pervasives_Native.None)
                     | uu____18076 -> FStar_Pervasives_Native.None))
               | uu____18079 -> FStar_Pervasives_Native.None in
             let is_forall_const phi =
               let uu____18092 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____18092 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv, uu____18098)::[], uu____18099, phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18119 = FStar_Syntax_Print.bv_to_string bv in
                       let uu____18121 =
                         FStar_Syntax_Print.term_to_string phi' in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18119
                         uu____18121)
                    else ();
                    is_quantified_const bv phi')
               | uu____18126 -> FStar_Pervasives_Native.None in
             let is_const_match phi =
               let uu____18141 =
                 let uu____18142 = FStar_Syntax_Subst.compress phi in
                 uu____18142.FStar_Syntax_Syntax.n in
               match uu____18141 with
               | FStar_Syntax_Syntax.Tm_match (uu____18148, br::brs) ->
                   let uu____18215 = br in
                   (match uu____18215 with
                    | (uu____18233, uu____18234, e) ->
                        let r =
                          let uu____18256 = simp_t e in
                          match uu____18256 with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18268 =
                                FStar_List.for_all
                                  (fun uu____18287 ->
                                     match uu____18287 with
                                     | (uu____18301, uu____18302, e') ->
                                         let uu____18316 = simp_t e' in
                                         uu____18316 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs in
                              if uu____18268
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None in
                        r)
               | uu____18332 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____18342 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____18342
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18378 =
                 match uu____18378 with
                 | (t1, q) ->
                     let uu____18399 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____18399 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
                      | uu____18431 -> (t1, q)) in
               let uu____18444 = FStar_Syntax_Util.head_and_args t in
               match uu____18444 with
               | (head, args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     t.FStar_Syntax_Syntax.pos in
             let rec clearly_inhabited ty =
               let uu____18522 =
                 let uu____18523 = FStar_Syntax_Util.unmeta ty in
                 uu____18523.FStar_Syntax_Syntax.n in
               match uu____18522 with
               | FStar_Syntax_Syntax.Tm_uinst (t, uu____18528) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18533, c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18557 -> false in
             let simplify arg =
               let uu____18590 = simp_t (FStar_Pervasives_Native.fst arg) in
               (uu____18590, arg) in
             let uu____18605 = is_forall_const tm1 in
             match uu____18605 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18611 = FStar_Syntax_Print.term_to_string tm1 in
                     let uu____18613 = FStar_Syntax_Print.term_to_string tm' in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18611
                       uu____18613)
                  else ();
                  (let uu____18618 = norm cfg env1 [] tm' in
                   maybe_simplify_aux cfg env1 stack1 uu____18618))
             | FStar_Pervasives_Native.None ->
                 let uu____18619 =
                   let uu____18620 = FStar_Syntax_Subst.compress tm1 in
                   uu____18620.FStar_Syntax_Syntax.n in
                 (match uu____18619 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18624;
                              FStar_Syntax_Syntax.vars = uu____18625;_},
                            uu____18626);
                         FStar_Syntax_Syntax.pos = uu____18627;
                         FStar_Syntax_Syntax.vars = uu____18628;_},
                       args)
                      ->
                      let uu____18658 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____18658
                      then
                        let uu____18661 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____18661 with
                         | (FStar_Pervasives_Native.Some (true), uu____18719)::
                             (uu____18720, (arg, uu____18722))::[] ->
                             maybe_auto_squash arg
                         | (uu____18795, (arg, uu____18797))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____18798)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____18871)::uu____18872::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18942::(FStar_Pervasives_Native.Some
                                         (false), uu____18943)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19013 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19031 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____19031
                         then
                           let uu____19034 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____19034 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____19092)::uu____19093::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19163::(FStar_Pervasives_Native.Some
                                           (true), uu____19164)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____19234)::(uu____19235, (arg, uu____19237))::[]
                               -> maybe_auto_squash arg
                           | (uu____19310, (arg, uu____19312))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____19313)::[]
                               -> maybe_auto_squash arg
                           | uu____19386 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19404 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____19404
                            then
                              let uu____19407 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____19407 with
                              | uu____19465::(FStar_Pervasives_Native.Some
                                              (true), uu____19466)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____19536)::uu____19537::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____19607)::(uu____19608,
                                                (arg, uu____19610))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19683, (p, uu____19685))::(uu____19686,
                                                                  (q,
                                                                   uu____19688))::[]
                                  ->
                                  let uu____19760 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____19760
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19765 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19783 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____19783
                               then
                                 let uu____19786 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____19786 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____19844)::(FStar_Pervasives_Native.Some
                                                   (true), uu____19845)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____19919)::(FStar_Pervasives_Native.Some
                                                   (false), uu____19920)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____19994)::(FStar_Pervasives_Native.Some
                                                   (false), uu____19995)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20069)::(FStar_Pervasives_Native.Some
                                                   (true), uu____20070)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20144, (arg, uu____20146))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____20147)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20220)::(uu____20221,
                                                   (arg, uu____20223))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20296, (arg, uu____20298))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____20299)::[]
                                     ->
                                     let uu____20372 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____20372
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20373)::(uu____20374,
                                                   (arg, uu____20376))::[]
                                     ->
                                     let uu____20449 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____20449
                                 | (uu____20450, (p, uu____20452))::(uu____20453,
                                                                    (q,
                                                                    uu____20455))::[]
                                     ->
                                     let uu____20527 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____20527
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20532 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20550 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____20550
                                  then
                                    let uu____20553 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____20553 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____20611)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____20655)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20699 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20717 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____20717
                                     then
                                       match args with
                                       | (t, uu____20721)::[] ->
                                           let uu____20746 =
                                             let uu____20747 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____20747.FStar_Syntax_Syntax.n in
                                           (match uu____20746 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20750::[], body,
                                                 uu____20752)
                                                ->
                                                let uu____20787 = simp_t body in
                                                (match uu____20787 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20793 -> tm1)
                                            | uu____20797 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20799))::(t, uu____20801)::[]
                                           ->
                                           let uu____20841 =
                                             let uu____20842 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____20842.FStar_Syntax_Syntax.n in
                                           (match uu____20841 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20845::[], body,
                                                 uu____20847)
                                                ->
                                                let uu____20882 = simp_t body in
                                                (match uu____20882 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20890 -> tm1)
                                            | uu____20894 -> tm1)
                                       | uu____20895 -> tm1
                                     else
                                       (let uu____20908 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____20908
                                        then
                                          match args with
                                          | (t, uu____20912)::[] ->
                                              let uu____20937 =
                                                let uu____20938 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____20938.FStar_Syntax_Syntax.n in
                                              (match uu____20937 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20941::[], body,
                                                    uu____20943)
                                                   ->
                                                   let uu____20978 =
                                                     simp_t body in
                                                   (match uu____20978 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20984 -> tm1)
                                               | uu____20988 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20990))::(t, uu____20992)::[]
                                              ->
                                              let uu____21032 =
                                                let uu____21033 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____21033.FStar_Syntax_Syntax.n in
                                              (match uu____21032 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21036::[], body,
                                                    uu____21038)
                                                   ->
                                                   let uu____21073 =
                                                     simp_t body in
                                                   (match uu____21073 with
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
                                                    | uu____21081 -> tm1)
                                               | uu____21085 -> tm1)
                                          | uu____21086 -> tm1
                                        else
                                          (let uu____21099 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____21099
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21102;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21103;_},
                                                uu____21104)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21130;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21131;_},
                                                uu____21132)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21158 -> tm1
                                           else
                                             (let uu____21171 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____21171
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____21185 =
                                                    let uu____21186 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____21186.FStar_Syntax_Syntax.n in
                                                  match uu____21185 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21197 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21211 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____21211
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____21250 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____21250
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21256 =
                                                         let uu____21257 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____21257.FStar_Syntax_Syntax.n in
                                                       match uu____21256 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21260 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____21268 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____21268
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21277
                                                                  =
                                                                  let uu____21278
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____21278.FStar_Syntax_Syntax.n in
                                                                match uu____21277
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____21284)
                                                                    -> hd
                                                                | uu____21309
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____21313
                                                                =
                                                                let uu____21324
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____21324] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21313)
                                                       | uu____21357 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21362 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____21362 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21382 ->
                                                     let uu____21391 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____21391 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21397;
                         FStar_Syntax_Syntax.vars = uu____21398;_},
                       args)
                      ->
                      let uu____21424 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____21424
                      then
                        let uu____21427 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____21427 with
                         | (FStar_Pervasives_Native.Some (true), uu____21485)::
                             (uu____21486, (arg, uu____21488))::[] ->
                             maybe_auto_squash arg
                         | (uu____21561, (arg, uu____21563))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____21564)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____21637)::uu____21638::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21708::(FStar_Pervasives_Native.Some
                                         (false), uu____21709)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21779 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21797 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____21797
                         then
                           let uu____21800 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____21800 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____21858)::uu____21859::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21929::(FStar_Pervasives_Native.Some
                                           (true), uu____21930)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____22000)::(uu____22001, (arg, uu____22003))::[]
                               -> maybe_auto_squash arg
                           | (uu____22076, (arg, uu____22078))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____22079)::[]
                               -> maybe_auto_squash arg
                           | uu____22152 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22170 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____22170
                            then
                              let uu____22173 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____22173 with
                              | uu____22231::(FStar_Pervasives_Native.Some
                                              (true), uu____22232)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____22302)::uu____22303::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____22373)::(uu____22374,
                                                (arg, uu____22376))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22449, (p, uu____22451))::(uu____22452,
                                                                  (q,
                                                                   uu____22454))::[]
                                  ->
                                  let uu____22526 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____22526
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22531 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22549 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____22549
                               then
                                 let uu____22552 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____22552 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____22610)::(FStar_Pervasives_Native.Some
                                                   (true), uu____22611)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____22685)::(FStar_Pervasives_Native.Some
                                                   (false), uu____22686)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____22760)::(FStar_Pervasives_Native.Some
                                                   (false), uu____22761)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____22835)::(FStar_Pervasives_Native.Some
                                                   (true), uu____22836)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22910, (arg, uu____22912))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____22913)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____22986)::(uu____22987,
                                                   (arg, uu____22989))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23062, (arg, uu____23064))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____23065)::[]
                                     ->
                                     let uu____23138 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____23138
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____23139)::(uu____23140,
                                                   (arg, uu____23142))::[]
                                     ->
                                     let uu____23215 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____23215
                                 | (uu____23216, (p, uu____23218))::(uu____23219,
                                                                    (q,
                                                                    uu____23221))::[]
                                     ->
                                     let uu____23293 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____23293
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23298 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23316 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____23316
                                  then
                                    let uu____23319 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____23319 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____23377)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____23421)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23465 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23483 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____23483
                                     then
                                       match args with
                                       | (t, uu____23487)::[] ->
                                           let uu____23512 =
                                             let uu____23513 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____23513.FStar_Syntax_Syntax.n in
                                           (match uu____23512 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23516::[], body,
                                                 uu____23518)
                                                ->
                                                let uu____23553 = simp_t body in
                                                (match uu____23553 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23559 -> tm1)
                                            | uu____23563 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23565))::(t, uu____23567)::[]
                                           ->
                                           let uu____23607 =
                                             let uu____23608 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____23608.FStar_Syntax_Syntax.n in
                                           (match uu____23607 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23611::[], body,
                                                 uu____23613)
                                                ->
                                                let uu____23648 = simp_t body in
                                                (match uu____23648 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23656 -> tm1)
                                            | uu____23660 -> tm1)
                                       | uu____23661 -> tm1
                                     else
                                       (let uu____23674 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____23674
                                        then
                                          match args with
                                          | (t, uu____23678)::[] ->
                                              let uu____23703 =
                                                let uu____23704 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____23704.FStar_Syntax_Syntax.n in
                                              (match uu____23703 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23707::[], body,
                                                    uu____23709)
                                                   ->
                                                   let uu____23744 =
                                                     simp_t body in
                                                   (match uu____23744 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23750 -> tm1)
                                               | uu____23754 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23756))::(t, uu____23758)::[]
                                              ->
                                              let uu____23798 =
                                                let uu____23799 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____23799.FStar_Syntax_Syntax.n in
                                              (match uu____23798 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23802::[], body,
                                                    uu____23804)
                                                   ->
                                                   let uu____23839 =
                                                     simp_t body in
                                                   (match uu____23839 with
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
                                                    | uu____23847 -> tm1)
                                               | uu____23851 -> tm1)
                                          | uu____23852 -> tm1
                                        else
                                          (let uu____23865 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____23865
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23868;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23869;_},
                                                uu____23870)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23896;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23897;_},
                                                uu____23898)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23924 -> tm1
                                           else
                                             (let uu____23937 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____23937
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____23951 =
                                                    let uu____23952 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____23952.FStar_Syntax_Syntax.n in
                                                  match uu____23951 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____23963 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____23977 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____23977
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____24012 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____24012
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24018 =
                                                         let uu____24019 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____24019.FStar_Syntax_Syntax.n in
                                                       match uu____24018 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24022 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____24030 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____24030
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24039
                                                                  =
                                                                  let uu____24040
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____24040.FStar_Syntax_Syntax.n in
                                                                match uu____24039
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____24046)
                                                                    -> hd
                                                                | uu____24071
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____24075
                                                                =
                                                                let uu____24086
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____24086] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24075)
                                                       | uu____24119 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24124 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____24124 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24144 ->
                                                     let uu____24153 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____24153 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
                      let uu____24164 = simp_t t in
                      (match uu____24164 with
                       | FStar_Pervasives_Native.Some (true) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false) -> tm1
                       | FStar_Pervasives_Native.None -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24173 ->
                      let uu____24196 = is_const_match tm1 in
                      (match uu____24196 with
                       | FStar_Pervasives_Native.Some (true) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None -> tm1)
                  | uu____24205 -> tm1))
and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24215 ->
               (let uu____24217 = FStar_Syntax_Print.tag_of_term t in
                let uu____24219 = FStar_Syntax_Print.term_to_string t in
                let uu____24221 =
                  FStar_Util.string_of_int (FStar_List.length env1) in
                let uu____24229 =
                  let uu____24231 =
                    let uu____24234 = firstn (Prims.of_int (4)) stack1 in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24234 in
                  stack_to_string uu____24231 in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24217 uu____24219 uu____24221 uu____24229);
               (let uu____24259 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild") in
                if uu____24259
                then
                  let uu____24263 = FStar_Syntax_Util.unbound_variables t in
                  match uu____24263 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24270 = FStar_Syntax_Print.tag_of_term t in
                        let uu____24272 = FStar_Syntax_Print.term_to_string t in
                        let uu____24274 =
                          let uu____24276 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string) in
                          FStar_All.pipe_right uu____24276
                            (FStar_String.concat ", ") in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24270
                          uu____24272 uu____24274);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t in
           let uu____24298 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____24306)::uu____24307 -> true
                | uu____24317 -> false) in
           if uu____24298
           then
             let uu____24320 = FStar_All.pipe_right f_opt FStar_Util.must in
             FStar_All.pipe_right uu____24320 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t in
              match stack1 with
              | [] -> t1
              | (Debug (tm, time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now () in
                      let uu____24334 =
                        let uu____24336 =
                          let uu____24338 =
                            FStar_Util.time_diff time_then time_now in
                          FStar_Pervasives_Native.snd uu____24338 in
                        FStar_Util.string_of_int uu____24336 in
                      let uu____24345 = FStar_Syntax_Print.term_to_string tm in
                      let uu____24347 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg in
                      let uu____24349 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24334 uu____24345 uu____24347 uu____24349)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____24358, m, r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24387 ->
                        let uu____24388 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24388);
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
                  let uu____24431 =
                    let uu___2855_24432 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2855_24432.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2855_24432.FStar_Syntax_Syntax.vars)
                    } in
                  rebuild cfg env1 stack2 uu____24431
              | (Arg
                  (Univ uu____24435, uu____24436, uu____24437))::uu____24438
                  -> failwith "Impossible"
              | (Arg (Dummy, uu____24442, uu____24443))::uu____24444 ->
                  failwith "Impossible"
              | (UnivArgs (us, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg, tm, uu____24460, uu____24461), aq, r))::stack2
                  when
                  let uu____24513 = head_of t1 in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24513 ->
                  let t2 =
                    let uu____24515 =
                      let uu____24516 = closure_as_term cfg env_arg tm in
                      (uu____24516, aq) in
                    FStar_Syntax_Syntax.extend_app t1 uu____24515 r in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg, tm, m, uu____24526), aq, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24581 ->
                        let uu____24582 =
                          FStar_Syntax_Print.term_to_string tm in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24582);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (let uu____24586 =
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          &&
                          (let uu____24589 = is_partial_primop_app cfg t1 in
                           Prims.op_Negation uu____24589) in
                      if uu____24586
                      then
                        let arg = closure_as_term cfg env_arg tm in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2 in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu____24605 = FStar_ST.op_Bang m in
                      match uu____24605 with
                      | FStar_Pervasives_Native.None ->
                          let uu____24679 =
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                              &&
                              (let uu____24682 = is_partial_primop_app cfg t1 in
                               Prims.op_Negation uu____24682) in
                          if uu____24679
                          then
                            let arg = closure_as_term cfg env_arg tm in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                            rebuild cfg env_arg stack2 t2
                          else
                            (let stack3 = (MemoLazy m) ::
                               (App (env1, t1, aq, r)) :: stack2 in
                             norm cfg env_arg stack3 tm)
                      | FStar_Pervasives_Native.Some (uu____24696, a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq) r in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2, head, aq, r))::stack' when
                  should_reify cfg stack1 ->
                  let t0 = t1 in
                  let fallback msg uu____24750 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____24755 ->
                         let uu____24756 =
                           FStar_Syntax_Print.term_to_string t1 in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____24756);
                    (let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                     rebuild cfg env2 stack' t2) in
                  let is_layered_effect m =
                    let uu____24771 =
                      FStar_All.pipe_right m
                        (FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv) in
                    FStar_All.pipe_right uu____24771
                      (FStar_TypeChecker_Env.is_layered_effect
                         cfg.FStar_TypeChecker_Cfg.tcenv) in
                  let uu____24773 =
                    let uu____24774 = FStar_Syntax_Subst.compress t1 in
                    uu____24774.FStar_Syntax_Syntax.n in
                  (match uu____24773 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____24777, FStar_Syntax_Syntax.Meta_monadic
                        (m, uu____24779))
                       when
                       (FStar_All.pipe_right m is_layered_effect) &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu____24789 =
                         let uu____24791 = FStar_Ident.string_of_lid m in
                         FStar_Util.format1
                           "Meta_monadic for a layered effect %s in non-extraction mode"
                           uu____24791 in
                       fallback uu____24789 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____24794, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, uu____24797))
                       when
                       ((is_layered_effect msrc) || (is_layered_effect mtgt))
                         &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu____24806 =
                         let uu____24808 = FStar_Ident.string_of_lid msrc in
                         let uu____24810 = FStar_Ident.string_of_lid mtgt in
                         FStar_Util.format2
                           "Meta_monadic_lift for layered effect %s ~> %s in non extraction mode"
                           uu____24808 uu____24810 in
                       fallback uu____24806 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, ty))
                       ->
                       let lifted =
                         let uu____24838 = closure_as_term cfg env2 ty in
                         reify_lift cfg t2 msrc mtgt uu____24838 in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____24842 ->
                             let uu____24843 =
                               FStar_Syntax_Print.term_to_string lifted in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____24843);
                        (let uu____24846 = FStar_List.tl stack1 in
                         norm cfg env2 uu____24846 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____24847);
                          FStar_Syntax_Syntax.pos = uu____24848;
                          FStar_Syntax_Syntax.vars = uu____24849;_},
                        (e, uu____24851)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____24890 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____24907 = FStar_Syntax_Util.head_and_args t1 in
                       (match uu____24907 with
                        | (hd, args) ->
                            let uu____24950 =
                              let uu____24951 = FStar_Syntax_Util.un_uinst hd in
                              uu____24951.FStar_Syntax_Syntax.n in
                            (match uu____24950 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____24955 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv in
                                 (match uu____24955 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____24958;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____24959;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____24960;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____24962;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____24963;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____24964;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____24965;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____25001 -> fallback " (3)" ())
                             | uu____25005 -> fallback " (4)" ()))
                   | uu____25007 -> fallback " (2)" ())
              | (App (env2, head, aq, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env', head, aq, r))::stack2 ->
                  let uu____25028 =
                    let uu____25029 =
                      let uu____25030 =
                        let uu____25037 =
                          let uu____25038 =
                            let uu____25070 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            (env1, t1, uu____25070, false) in
                          Clos uu____25038 in
                        (uu____25037, aq, (t1.FStar_Syntax_Syntax.pos)) in
                      Arg uu____25030 in
                    uu____25029 :: stack2 in
                  norm cfg env' uu____25028 head
              | (Match (env', branches1, cfg1, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25145 ->
                        let uu____25146 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25146);
                   (let scrutinee_env = env1 in
                    let env2 = env' in
                    let scrutinee = t1 in
                    let norm_and_rebuild_match uu____25157 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25162 ->
                           let uu____25163 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           let uu____25165 =
                             let uu____25167 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____25197 ->
                                       match uu____25197 with
                                       | (p, uu____25208, uu____25209) ->
                                           FStar_Syntax_Print.pat_to_string p)) in
                             FStar_All.pipe_right uu____25167
                               (FStar_String.concat "\n\t") in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25163 uu____25165);
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
                                   (fun uu___16_25234 ->
                                      match uu___16_25234 with
                                      | FStar_TypeChecker_Env.InliningDelta
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                          -> true
                                      | uu____25238 -> false)) in
                            let steps =
                              let uu___3049_25241 =
                                cfg1.FStar_TypeChecker_Cfg.steps in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3049_25241.FStar_TypeChecker_Cfg.for_extraction)
                              } in
                            let uu___3052_25248 = cfg1 in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3052_25248.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3052_25248.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3052_25248.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3052_25248.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3052_25248.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3052_25248.FStar_TypeChecker_Cfg.reifying)
                            }) in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2 in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25323 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                             let uu____25354 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25443 ->
                                       fun uu____25444 ->
                                         match (uu____25443, uu____25444)
                                         with
                                         | ((pats1, env4), (p1, b)) ->
                                             let uu____25594 =
                                               norm_pat env4 p1 in
                                             (match uu____25594 with
                                              | (p2, env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3)) in
                             (match uu____25354 with
                              | (pats1, env4) ->
                                  ((let uu___3080_25764 = p in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3080_25764.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3084_25785 = x in
                               let uu____25786 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3084_25785.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3084_25785.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25786
                               } in
                             ((let uu___3087_25800 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3087_25800.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3091_25811 = x in
                               let uu____25812 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3091_25811.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3091_25811.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25812
                               } in
                             ((let uu___3094_25826 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3094_25826.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                             let x1 =
                               let uu___3100_25842 = x in
                               let uu____25843 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3100_25842.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3100_25842.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25843
                               } in
                             let t3 = norm_or_whnf env3 t2 in
                             ((let uu___3104_25858 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3104_25858.FStar_Syntax_Syntax.p)
                               }), env3) in
                       let branches2 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____25902 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch ->
                                     let uu____25932 =
                                       FStar_Syntax_Subst.open_branch branch in
                                     match uu____25932 with
                                     | (p, wopt, e) ->
                                         let uu____25952 = norm_pat env2 p in
                                         (match uu____25952 with
                                          | (p1, env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26007 =
                                                      norm_or_whnf env3 w in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26007 in
                                              let e1 = norm_or_whnf env3 e in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1)))) in
                       let scrutinee1 =
                         let uu____26024 =
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
                         if uu____26024
                         then
                           norm
                             (let uu___3123_26031 = cfg1 in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3125_26034 =
                                     cfg1.FStar_TypeChecker_Cfg.steps in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3125_26034.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3123_26031.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee in
                       let uu____26038 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches2)) r in
                       rebuild cfg1 env2 stack2 uu____26038) in
                    let rec is_cons head =
                      let uu____26064 =
                        let uu____26065 = FStar_Syntax_Subst.compress head in
                        uu____26065.FStar_Syntax_Syntax.n in
                      match uu____26064 with
                      | FStar_Syntax_Syntax.Tm_uinst (h, uu____26070) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26075 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26077;
                            FStar_Syntax_Syntax.fv_delta = uu____26078;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor);_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26080;
                            FStar_Syntax_Syntax.fv_delta = uu____26081;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26082);_}
                          -> true
                      | uu____26090 -> false in
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
                      let uu____26259 =
                        FStar_Syntax_Util.head_and_args scrutinee2 in
                      match uu____26259 with
                      | (head, args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26356 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26398 ->
                                    let uu____26399 =
                                      let uu____26401 = is_cons head in
                                      Prims.op_Negation uu____26401 in
                                    FStar_Util.Inr uu____26399)
                           | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                               let uu____26430 =
                                 let uu____26431 =
                                   FStar_Syntax_Util.un_uinst head in
                                 uu____26431.FStar_Syntax_Syntax.n in
                               (match uu____26430 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26450 ->
                                    let uu____26451 =
                                      let uu____26453 = is_cons head in
                                      Prims.op_Negation uu____26453 in
                                    FStar_Util.Inr uu____26451))
                    and matches_args out a p =
                      match (a, p) with
                      | ([], []) -> FStar_Util.Inl out
                      | ((t2, uu____26544)::rest_a,
                         (p1, uu____26547)::rest_p) ->
                          let uu____26606 = matches_pat t2 p1 in
                          (match uu____26606 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26659 -> FStar_Util.Inr false in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1, wopt, b)::rest ->
                          let uu____26782 = matches_pat scrutinee1 p1 in
                          (match uu____26782 with
                           | FStar_Util.Inr (false) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____26828 ->
                                     let uu____26829 =
                                       FStar_Syntax_Print.pat_to_string p1 in
                                     let uu____26831 =
                                       let uu____26833 =
                                         FStar_List.map
                                           (fun uu____26845 ->
                                              match uu____26845 with
                                              | (uu____26851, t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s in
                                       FStar_All.pipe_right uu____26833
                                         (FStar_String.concat "; ") in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____26829 uu____26831);
                                (let env0 = env2 in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3 ->
                                        fun uu____26887 ->
                                          match uu____26887 with
                                          | (bv, t2) ->
                                              let uu____26910 =
                                                let uu____26917 =
                                                  let uu____26920 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv in
                                                  FStar_Pervasives_Native.Some
                                                    uu____26920 in
                                                let uu____26921 =
                                                  let uu____26922 =
                                                    let uu____26954 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2)) in
                                                    ([], t2, uu____26954,
                                                      false) in
                                                  Clos uu____26922 in
                                                (uu____26917, uu____26921) in
                                              uu____26910 :: env3) env2 s in
                                 let uu____27047 =
                                   guard_when_clause wopt b rest in
                                 norm cfg1 env3 stack2 uu____27047))) in
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
            (fun uu____27080 ->
               let uu____27081 = FStar_TypeChecker_Cfg.cfg_to_string c in
               FStar_Util.print1 "Cfg = %s\n" uu____27081);
          (let uu____27084 = is_nbe_request s in
           if uu____27084
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27090 ->
                   let uu____27091 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27091);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27097 ->
                   let uu____27098 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27098);
              (let uu____27101 =
                 FStar_Util.record_time (fun uu____27108 -> nbe_eval c s t) in
               match uu____27101 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27117 ->
                         let uu____27118 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____27120 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27118 uu____27120);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27128 ->
                   let uu____27129 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27129);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27135 ->
                   let uu____27136 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27136);
              (let uu____27139 =
                 FStar_Util.record_time (fun uu____27146 -> norm c [] [] t) in
               match uu____27139 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27161 ->
                         let uu____27162 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____27164 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27162 uu____27164);
                    r))))
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        let uu____27183 =
          let uu____27187 =
            let uu____27189 = FStar_TypeChecker_Env.current_module e in
            FStar_Ident.string_of_lid uu____27189 in
          FStar_Pervasives_Native.Some uu____27187 in
        FStar_Profiling.profile
          (fun uu____27192 -> normalize_with_primitive_steps [] s e t)
          uu____27183 "FStar.TypeChecker.Normalize"
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
          (fun uu____27214 ->
             let uu____27215 = FStar_Syntax_Print.comp_to_string c in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27215);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27221 ->
             let uu____27222 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27222);
        (let uu____27225 =
           FStar_Util.record_time (fun uu____27232 -> norm_comp cfg [] c) in
         match uu____27225 with
         | (c1, ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27247 ->
                   let uu____27248 = FStar_Syntax_Print.comp_to_string c1 in
                   let uu____27250 = FStar_Util.string_of_int ms in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27248
                     uu____27250);
              c1))
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1 ->
    fun u ->
      let uu____27264 = FStar_TypeChecker_Cfg.config [] env1 in
      norm_universe uu____27264 [] u
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
      let uu____27286 = normalize steps env1 t in
      FStar_TypeChecker_Env.non_informative env1 uu____27286
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1 ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27298 -> c
      | FStar_Syntax_Syntax.GTotal (t, uopt) when non_info_norm env1 t ->
          let uu___3293_27317 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3293_27317.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3293_27317.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____27324 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ) in
          if uu____27324
          then
            let ct1 =
              let uu____27328 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name in
              match uu____27328 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27335 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu____27335
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___3303_27342 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3303_27342.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3303_27342.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3303_27342.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c in
                  let uu___3307_27344 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3307_27344.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3307_27344.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3307_27344.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3307_27344.FStar_Syntax_Syntax.flags)
                  } in
            let uu___3310_27345 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3310_27345.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3310_27345.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27348 -> c
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1 ->
    fun lc ->
      let uu____27360 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ) in
      if uu____27360
      then
        let uu____27363 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name in
        match uu____27363 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3318_27367 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g -> g) lc in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3318_27367.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3318_27367.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3318_27367.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None -> lc
      else lc
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1 ->
    fun t ->
      let t1 =
        try
          (fun uu___3325_27386 ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3324_27389 ->
            ((let uu____27391 =
                let uu____27397 =
                  let uu____27399 = FStar_Util.message_of_exn uu___3324_27389 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27399 in
                (FStar_Errors.Warning_NormalizationFailure, uu____27397) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27391);
             t) in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1 ->
    fun c ->
      let c1 =
        try
          (fun uu___3335_27418 ->
             match () with
             | () ->
                 let uu____27419 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1 in
                 norm_comp uu____27419 [] c) ()
        with
        | uu___3334_27428 ->
            ((let uu____27430 =
                let uu____27436 =
                  let uu____27438 = FStar_Util.message_of_exn uu___3334_27428 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27438 in
                (FStar_Errors.Warning_NormalizationFailure, uu____27436) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27430);
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
                   let uu____27487 =
                     let uu____27488 =
                       let uu____27495 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi in
                       (y, uu____27495) in
                     FStar_Syntax_Syntax.Tm_refine uu____27488 in
                   FStar_Syntax_Syntax.mk uu____27487
                     t01.FStar_Syntax_Syntax.pos
               | uu____27500 -> t2)
          | uu____27501 -> t2 in
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
        let uu____27595 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____27595 with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu____27608 ->
                 let uu____27609 = FStar_Syntax_Util.abs_formals e in
                 (match uu____27609 with
                  | (actuals, uu____27619, uu____27620) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27640 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____27640 with
                         | (binders, args) ->
                             let uu____27651 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____27651
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
      | uu____27666 ->
          let uu____27667 = FStar_Syntax_Util.head_and_args t in
          (match uu____27667 with
           | (head, args) ->
               let uu____27710 =
                 let uu____27711 = FStar_Syntax_Subst.compress head in
                 uu____27711.FStar_Syntax_Syntax.n in
               (match uu____27710 with
                | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
                    let uu____27732 =
                      let uu____27739 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ in
                      FStar_Syntax_Util.arrow_formals uu____27739 in
                    (match uu____27732 with
                     | (formals, _tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27763 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3405_27771 = env1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3405_27771.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3405_27771.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3405_27771.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3405_27771.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3405_27771.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3405_27771.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3405_27771.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3405_27771.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3405_27771.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3405_27771.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3405_27771.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3405_27771.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3405_27771.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3405_27771.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3405_27771.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3405_27771.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3405_27771.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3405_27771.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3405_27771.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3405_27771.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3405_27771.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3405_27771.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3405_27771.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3405_27771.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3405_27771.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3405_27771.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3405_27771.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3405_27771.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3405_27771.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3405_27771.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3405_27771.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3405_27771.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3405_27771.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3405_27771.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3405_27771.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3405_27771.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3405_27771.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3405_27771.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3405_27771.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3405_27771.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3405_27771.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3405_27771.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3405_27771.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___3405_27771.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) t in
                            match uu____27763 with
                            | (uu____27774, ty, uu____27776) ->
                                eta_expand_with_type env1 t ty))
                | uu____27777 ->
                    let uu____27778 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3412_27786 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3412_27786.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3412_27786.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3412_27786.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3412_27786.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3412_27786.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3412_27786.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3412_27786.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3412_27786.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3412_27786.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3412_27786.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3412_27786.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3412_27786.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3412_27786.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3412_27786.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3412_27786.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3412_27786.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3412_27786.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3412_27786.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3412_27786.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3412_27786.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3412_27786.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3412_27786.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3412_27786.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3412_27786.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3412_27786.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3412_27786.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3412_27786.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3412_27786.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3412_27786.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3412_27786.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3412_27786.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3412_27786.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3412_27786.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3412_27786.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3412_27786.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3412_27786.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3412_27786.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3412_27786.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3412_27786.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3412_27786.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3412_27786.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3412_27786.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3412_27786.FStar_TypeChecker_Env.erasable_types_tab);
                           FStar_TypeChecker_Env.enable_defer_to_tac =
                             (uu___3412_27786.FStar_TypeChecker_Env.enable_defer_to_tac)
                         }) t in
                    (match uu____27778 with
                     | (uu____27789, ty, uu____27791) ->
                         eta_expand_with_type env1 t ty)))
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___3424_27873 = x in
      let uu____27874 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3424_27873.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3424_27873.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27874
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27877 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27893 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27894 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27895 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27896 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27903 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27904 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27905 -> t1
    | FStar_Syntax_Syntax.Tm_unknown -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu___3450_27939 = rc in
          let uu____27940 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____27949 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3450_27939.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27940;
            FStar_Syntax_Syntax.residual_flags = uu____27949
          } in
        let uu____27952 =
          let uu____27953 =
            let uu____27972 = elim_delayed_subst_binders bs in
            let uu____27981 = elim_delayed_subst_term t2 in
            let uu____27984 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____27972, uu____27981, uu____27984) in
          FStar_Syntax_Syntax.Tm_abs uu____27953 in
        mk uu____27952
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____28021 =
          let uu____28022 =
            let uu____28037 = elim_delayed_subst_binders bs in
            let uu____28046 = elim_delayed_subst_comp c in
            (uu____28037, uu____28046) in
          FStar_Syntax_Syntax.Tm_arrow uu____28022 in
        mk uu____28021
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu____28065 =
          let uu____28066 =
            let uu____28073 = elim_bv bv in
            let uu____28074 = elim_delayed_subst_term phi in
            (uu____28073, uu____28074) in
          FStar_Syntax_Syntax.Tm_refine uu____28066 in
        mk uu____28065
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu____28105 =
          let uu____28106 =
            let uu____28123 = elim_delayed_subst_term t2 in
            let uu____28126 = elim_delayed_subst_args args in
            (uu____28123, uu____28126) in
          FStar_Syntax_Syntax.Tm_app uu____28106 in
        mk uu____28105
    | FStar_Syntax_Syntax.Tm_match (t2, branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3472_28198 = p in
              let uu____28199 =
                let uu____28200 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____28200 in
              {
                FStar_Syntax_Syntax.v = uu____28199;
                FStar_Syntax_Syntax.p =
                  (uu___3472_28198.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3476_28202 = p in
              let uu____28203 =
                let uu____28204 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____28204 in
              {
                FStar_Syntax_Syntax.v = uu____28203;
                FStar_Syntax_Syntax.p =
                  (uu___3476_28202.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___3482_28211 = p in
              let uu____28212 =
                let uu____28213 =
                  let uu____28220 = elim_bv x in
                  let uu____28221 = elim_delayed_subst_term t0 in
                  (uu____28220, uu____28221) in
                FStar_Syntax_Syntax.Pat_dot_term uu____28213 in
              {
                FStar_Syntax_Syntax.v = uu____28212;
                FStar_Syntax_Syntax.p =
                  (uu___3482_28211.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___3488_28246 = p in
              let uu____28247 =
                let uu____28248 =
                  let uu____28262 =
                    FStar_List.map
                      (fun uu____28288 ->
                         match uu____28288 with
                         | (x, b) ->
                             let uu____28305 = elim_pat x in (uu____28305, b))
                      pats in
                  (fv, uu____28262) in
                FStar_Syntax_Syntax.Pat_cons uu____28248 in
              {
                FStar_Syntax_Syntax.v = uu____28247;
                FStar_Syntax_Syntax.p =
                  (uu___3488_28246.FStar_Syntax_Syntax.p)
              }
          | uu____28320 -> p in
        let elim_branch uu____28344 =
          match uu____28344 with
          | (pat, wopt, t3) ->
              let uu____28370 = elim_pat pat in
              let uu____28373 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____28376 = elim_delayed_subst_term t3 in
              (uu____28370, uu____28373, uu____28376) in
        let uu____28381 =
          let uu____28382 =
            let uu____28405 = elim_delayed_subst_term t2 in
            let uu____28408 = FStar_List.map elim_branch branches1 in
            (uu____28405, uu____28408) in
          FStar_Syntax_Syntax.Tm_match uu____28382 in
        mk uu____28381
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let elim_ascription uu____28539 =
          match uu____28539 with
          | (tc, topt) ->
              let uu____28574 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28584 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____28584
                | FStar_Util.Inr c ->
                    let uu____28586 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____28586 in
              let uu____28587 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____28574, uu____28587) in
        let uu____28596 =
          let uu____28597 =
            let uu____28624 = elim_delayed_subst_term t2 in
            let uu____28627 = elim_ascription a in
            (uu____28624, uu____28627, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____28597 in
        mk uu____28596
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu___3518_28690 = lb in
          let uu____28691 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____28694 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3518_28690.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3518_28690.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28691;
            FStar_Syntax_Syntax.lbeff =
              (uu___3518_28690.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28694;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3518_28690.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3518_28690.FStar_Syntax_Syntax.lbpos)
          } in
        let uu____28697 =
          let uu____28698 =
            let uu____28712 =
              let uu____28720 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____28720) in
            let uu____28732 = elim_delayed_subst_term t2 in
            (uu____28712, uu____28732) in
          FStar_Syntax_Syntax.Tm_let uu____28698 in
        mk uu____28697
    | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
        mk (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi in
        let uu____28777 =
          let uu____28778 =
            let uu____28785 = elim_delayed_subst_term tm in
            (uu____28785, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu____28778 in
        mk uu____28777
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu____28796 =
          let uu____28797 =
            let uu____28804 = elim_delayed_subst_term t2 in
            let uu____28807 = elim_delayed_subst_meta md in
            (uu____28804, uu____28807) in
          FStar_Syntax_Syntax.Tm_meta uu____28797 in
        mk uu____28796
and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_List.map
      (fun uu___17_28816 ->
         match uu___17_28816 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28820 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____28820
         | f -> f) flags
and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c ->
    let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uopt) ->
        let uu____28843 =
          let uu____28844 =
            let uu____28853 = elim_delayed_subst_term t in
            (uu____28853, uopt) in
          FStar_Syntax_Syntax.Total uu____28844 in
        mk uu____28843
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uu____28870 =
          let uu____28871 =
            let uu____28880 = elim_delayed_subst_term t in
            (uu____28880, uopt) in
          FStar_Syntax_Syntax.GTotal uu____28871 in
        mk uu____28870
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3551_28889 = ct in
          let uu____28890 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____28893 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____28904 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3551_28889.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3551_28889.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28890;
            FStar_Syntax_Syntax.effect_args = uu____28893;
            FStar_Syntax_Syntax.flags = uu____28904
          } in
        mk (FStar_Syntax_Syntax.Comp ct1)
and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_28907 ->
    match uu___18_28907 with
    | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
        let uu____28942 =
          let uu____28963 = FStar_List.map elim_delayed_subst_term names in
          let uu____28972 = FStar_List.map elim_delayed_subst_args args in
          (uu____28963, uu____28972) in
        FStar_Syntax_Syntax.Meta_pattern uu____28942
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____29027 =
          let uu____29034 = elim_delayed_subst_term t in (m, uu____29034) in
        FStar_Syntax_Syntax.Meta_monadic uu____29027
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu____29046 =
          let uu____29055 = elim_delayed_subst_term t in
          (m1, m2, uu____29055) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29046
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
      (fun uu____29088 ->
         match uu____29088 with
         | (t, q) ->
             let uu____29107 = elim_delayed_subst_term t in (uu____29107, q))
      args
and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun uu____29135 ->
         match uu____29135 with
         | (x, q) ->
             let uu____29154 =
               let uu___3577_29155 = x in
               let uu____29156 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3577_29155.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3577_29155.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29156
               } in
             (uu____29154, q)) bs
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
            | (uu____29264, FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  c.FStar_Syntax_Syntax.pos
            | (uu____29296, FStar_Util.Inl t) ->
                let uu____29318 =
                  let uu____29319 =
                    let uu____29334 = FStar_Syntax_Syntax.mk_Total t in
                    (binders, uu____29334) in
                  FStar_Syntax_Syntax.Tm_arrow uu____29319 in
                FStar_Syntax_Syntax.mk uu____29318 t.FStar_Syntax_Syntax.pos in
          let uu____29347 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____29347 with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env1 t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____29379 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29452 ->
                    let uu____29453 =
                      let uu____29462 =
                        let uu____29463 = FStar_Syntax_Subst.compress t4 in
                        uu____29463.FStar_Syntax_Syntax.n in
                      (uu____29462, tc) in
                    (match uu____29453 with
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inr uu____29492) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inl uu____29539) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29584, FStar_Util.Inl uu____29585) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29616 -> failwith "Impossible") in
              (match uu____29379 with
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
          let uu____29755 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t) in
          match uu____29755 with
          | (univ_names1, binders1, tc) ->
              let uu____29829 = FStar_Util.left tc in
              (univ_names1, binders1, uu____29829)
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
          let uu____29883 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c) in
          match uu____29883 with
          | (univ_names1, binders1, tc) ->
              let uu____29957 = FStar_Util.right tc in
              (univ_names1, binders1, uu____29957)
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1 ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univ_names, binders, typ, lids, lids') ->
          let uu____29999 = elim_uvars_aux_t env1 univ_names binders typ in
          (match uu____29999 with
           | (univ_names1, binders1, typ1) ->
               let uu___3660_30039 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3660_30039.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3660_30039.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3660_30039.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3660_30039.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3660_30039.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
          let uu___3666_30054 = s in
          let uu____30055 =
            let uu____30056 =
              let uu____30065 = FStar_List.map (elim_uvars env1) sigs in
              (uu____30065, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____30056 in
          {
            FStar_Syntax_Syntax.sigel = uu____30055;
            FStar_Syntax_Syntax.sigrng =
              (uu___3666_30054.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3666_30054.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3666_30054.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3666_30054.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3666_30054.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univ_names, typ, lident, i, lids) ->
          let uu____30084 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____30084 with
           | (univ_names1, uu____30108, typ1) ->
               let uu___3680_30130 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3680_30130.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3680_30130.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3680_30130.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3680_30130.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3680_30130.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) ->
          let uu____30137 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____30137 with
           | (univ_names1, uu____30161, typ1) ->
               let uu___3691_30183 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3691_30183.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3691_30183.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3691_30183.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3691_30183.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3691_30183.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____30213 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____30213 with
                    | (opening, lbunivs) ->
                        let elim t =
                          let uu____30238 =
                            let uu____30239 =
                              let uu____30240 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env1 uu____30240 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30239 in
                          elim_delayed_subst_term uu____30238 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___3707_30243 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3707_30243.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3707_30243.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3707_30243.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3707_30243.FStar_Syntax_Syntax.lbpos)
                        })) in
          let uu___3710_30244 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3710_30244.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3710_30244.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3710_30244.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3710_30244.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3710_30244.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l, us, t) ->
          let uu____30253 = elim_uvars_aux_t env1 us [] t in
          (match uu____30253 with
           | (us1, uu____30277, t1) ->
               let uu___3721_30299 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3721_30299.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3721_30299.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3721_30299.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3721_30299.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3721_30299.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30301 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit in
          (match uu____30301 with
           | (univs, binders, uu____30320) ->
               let uu____30341 =
                 let uu____30346 = FStar_Syntax_Subst.univ_var_opening univs in
                 match uu____30346 with
                 | (univs_opening, univs1) ->
                     let uu____30369 =
                       FStar_Syntax_Subst.univ_var_closing univs1 in
                     (univs_opening, uu____30369) in
               (match uu____30341 with
                | (univs_opening, univs_closing) ->
                    let uu____30372 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____30378 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____30379 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____30378, uu____30379) in
                    (match uu____30372 with
                     | (b_opening, b_closing) ->
                         let n = FStar_List.length univs in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____30405 =
                           match uu____30405 with
                           | (us, t) ->
                               let n_us = FStar_List.length us in
                               let uu____30423 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____30423 with
                                | (us1, t1) ->
                                    let uu____30434 =
                                      let uu____30443 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____30448 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____30443, uu____30448) in
                                    (match uu____30434 with
                                     | (b_opening1, b_closing1) ->
                                         let uu____30471 =
                                           let uu____30480 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           let uu____30485 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           (uu____30480, uu____30485) in
                                         (match uu____30471 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30509 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30509 in
                                              let uu____30510 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2 in
                                              (match uu____30510 with
                                               | (uu____30537, uu____30538,
                                                  t3) ->
                                                   let t4 =
                                                     let uu____30561 =
                                                       let uu____30562 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30562 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30561 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____30571 =
                             elim_uvars_aux_t env1 univs binders t in
                           match uu____30571 with
                           | (uu____30590, uu____30591, t1) -> t1 in
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
                             | uu____30667 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____30694 =
                               let uu____30695 =
                                 FStar_Syntax_Subst.compress body in
                               uu____30695.FStar_Syntax_Syntax.n in
                             match uu____30694 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,
                                  (FStar_Util.Inl typ,
                                   FStar_Pervasives_Native.None),
                                  FStar_Pervasives_Native.None)
                                 -> (defn, typ)
                             | uu____30754 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____30788 =
                               let uu____30789 =
                                 FStar_Syntax_Subst.compress t in
                               uu____30789.FStar_Syntax_Syntax.n in
                             match uu____30788 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars, body, uu____30812) ->
                                 let uu____30837 = destruct_action_body body in
                                 (match uu____30837 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu____30886 ->
                                 let uu____30887 = destruct_action_body t in
                                 (match uu____30887 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu____30942 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____30942 with
                           | (action_univs, t) ->
                               let uu____30951 = destruct_action_typ_templ t in
                               (match uu____30951 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      let uu___3805_30998 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3805_30998.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3805_30998.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3808_31000 = ed in
                           let uu____31001 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature in
                           let uu____31002 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu____31003 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3808_31000.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3808_31000.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31001;
                             FStar_Syntax_Syntax.combinators = uu____31002;
                             FStar_Syntax_Syntax.actions = uu____31003;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3808_31000.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let uu___3811_31006 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3811_31006.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3811_31006.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3811_31006.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3811_31006.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3811_31006.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31027 =
            match uu___19_31027 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu____31058 = elim_uvars_aux_t env1 us [] t in
                (match uu____31058 with
                 | (us1, uu____31090, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___3826_31121 = sub_eff in
            let uu____31122 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____31125 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___3826_31121.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3826_31121.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31122;
              FStar_Syntax_Syntax.lift = uu____31125
            } in
          let uu___3829_31128 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3829_31128.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3829_31128.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3829_31128.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3829_31128.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3829_31128.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, univ_names, binders, comp, flags) ->
          let uu____31138 = elim_uvars_aux_c env1 univ_names binders comp in
          (match uu____31138 with
           | (univ_names1, binders1, comp1) ->
               let uu___3842_31178 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3842_31178.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3842_31178.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3842_31178.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3842_31178.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3842_31178.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31181 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31182 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31195 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m, n, p, (us_t, t), (us_ty, ty)) ->
          let uu____31225 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____31225 with
           | (us_t1, uu____31249, t1) ->
               let uu____31271 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____31271 with
                | (us_ty1, uu____31295, ty1) ->
                    let uu___3869_31317 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3869_31317.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3869_31317.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3869_31317.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3869_31317.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3869_31317.FStar_Syntax_Syntax.sigopts)
                    }))
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          (m, n, (us_t, t), (us_ty, ty)) ->
          let uu____31348 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____31348 with
           | (us_t1, uu____31372, t1) ->
               let uu____31394 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____31394 with
                | (us_ty1, uu____31418, ty1) ->
                    let uu___3889_31440 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                           (m, n, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3889_31440.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3889_31440.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3889_31440.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3889_31440.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3889_31440.FStar_Syntax_Syntax.sigopts)
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
        let uu____31491 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu____31491 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31513 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
            (match uu____31513 with
             | (uu____31520, head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     t.FStar_Syntax_Syntax.pos in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env1 t' in
                 FStar_Pervasives_Native.Some t'1) in
      let uu____31524 = FStar_Syntax_Util.head_and_args t in
      match uu____31524 with
      | (head, args) ->
          let uu____31569 =
            let uu____31570 = FStar_Syntax_Subst.compress head in
            uu____31570.FStar_Syntax_Syntax.n in
          (match uu____31569 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31577;
                  FStar_Syntax_Syntax.vars = uu____31578;_},
                us)
               -> aux fv us args
           | uu____31584 -> FStar_Pervasives_Native.None)
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
          let uu____31647 = FStar_Syntax_Util.arrow_formals_comp t1 in
          match uu____31647 with
          | (bs, c) ->
              let len = FStar_List.length bs in
              (match (bs, c) with
               | ([], uu____31683) when retry ->
                   let uu____31702 = unfold_whnf env1 t1 in
                   aux false n1 uu____31702
               | ([], uu____31704) when Prims.op_Negation retry -> (bs, c)
               | (bs1, c1) when len = n1 -> (bs1, c1)
               | (bs1, c1) when len > n1 ->
                   let uu____31772 = FStar_List.splitAt n1 bs1 in
                   (match uu____31772 with
                    | (bs_l, bs_r) ->
                        let uu____31839 =
                          let uu____31840 = FStar_Syntax_Util.arrow bs_r c1 in
                          FStar_Syntax_Syntax.mk_Total uu____31840 in
                        (bs_l, uu____31839))
               | (bs1, c1) when
                   ((len < n1) && (FStar_Syntax_Util.is_total_comp c1)) &&
                     (let uu____31866 = FStar_Syntax_Util.has_decreases c1 in
                      Prims.op_Negation uu____31866)
                   ->
                   let uu____31868 =
                     aux true (n1 - len) (FStar_Syntax_Util.comp_result c1) in
                   (match uu____31868 with
                    | (bs', c') -> ((FStar_List.append bs1 bs'), c'))
               | (bs1, c1) -> (bs1, c1)) in
        aux true n t