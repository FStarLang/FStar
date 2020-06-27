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
    match projectee with | Clos _0 -> true | uu____155 -> false
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee -> match projectee with | Clos _0 -> _0
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee ->
    match projectee with | Univ _0 -> true | uu____267 -> false
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee -> match projectee with | Dummy -> true | uu____285 -> false
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
  fun projectee -> match projectee with | Arg _0 -> true | uu____493 -> false
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivArgs _0 -> true | uu____536 -> false
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | MemoLazy _0 -> true | uu____579 -> false
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____624 -> false
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu____679 -> false
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu____742 -> false
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | App _0 -> _0
let (uu___is_CBVApp : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | CBVApp _0 -> true | uu____793 -> false
let (__proj__CBVApp__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | CBVApp _0 -> _0
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____842 -> false
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu____887 -> false
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Cfg _0 -> true | uu____930 -> false
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee -> match projectee with | Cfg _0 -> _0
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | Debug _0 -> true | uu____953 -> false
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____982 = FStar_Syntax_Util.head_and_args' t in
    match uu____982 with | (hd, uu____998) -> hd
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg ->
    fun r ->
      fun t ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu____1049 = FStar_ST.op_Bang r in
          match uu____1049 with
          | FStar_Pervasives_Native.Some uu____1075 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let (closure_to_string : closure -> Prims.string) =
  fun uu___1_1108 ->
    match uu___1_1108 with
    | Clos (env1, t, uu____1112, uu____1113) ->
        let uu____1160 =
          FStar_All.pipe_right (FStar_List.length env1)
            FStar_Util.string_of_int in
        let uu____1170 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1160 uu____1170
    | Univ uu____1173 -> "Univ"
    | Dummy -> "dummy"
let (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env1 ->
    let uu____1199 =
      FStar_List.map
        (fun uu____1215 ->
           match uu____1215 with
           | (bopt, c) ->
               let uu____1229 =
                 match bopt with
                 | FStar_Pervasives_Native.None -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x in
               let uu____1234 = closure_to_string c in
               FStar_Util.format2 "(%s, %s)" uu____1229 uu____1234) env1 in
    FStar_All.pipe_right uu____1199 (FStar_String.concat "; ")
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1248 ->
    match uu___2_1248 with
    | Arg (c, uu____1251, uu____1252) ->
        let uu____1253 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1253
    | MemoLazy uu____1256 -> "MemoLazy"
    | Abs (uu____1264, bs, uu____1266, uu____1267, uu____1268) ->
        let uu____1273 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1273
    | UnivArgs uu____1284 -> "UnivArgs"
    | Match uu____1292 -> "Match"
    | App (uu____1302, t, uu____1304, uu____1305) ->
        let uu____1306 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1306
    | CBVApp (uu____1309, t, uu____1311, uu____1312) ->
        let uu____1313 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "CBVApp %s" uu____1313
    | Meta (uu____1316, m, uu____1318) -> "Meta"
    | Let uu____1320 -> "Let"
    | Cfg uu____1330 -> "Cfg"
    | Debug (t, uu____1333) ->
        let uu____1334 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1334
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s ->
    let uu____1348 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1348 (FStar_String.concat "; ")
let is_empty : 'uuuuuu1363 . 'uuuuuu1363 Prims.list -> Prims.bool =
  fun uu___3_1371 ->
    match uu___3_1371 with | [] -> true | uu____1375 -> false
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env1 ->
    fun x ->
      try
        (fun uu___119_1408 ->
           match () with
           | () ->
               let uu____1409 =
                 FStar_List.nth env1 x.FStar_Syntax_Syntax.index in
               FStar_Pervasives_Native.snd uu____1409) ()
      with
      | uu___118_1426 ->
          let uu____1427 =
            let uu____1429 = FStar_Syntax_Print.db_to_string x in
            let uu____1431 = env_to_string env1 in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1429
              uu____1431 in
          failwith uu____1427
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l ->
    let uu____1442 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid in
    if uu____1442
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1449 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid in
       if uu____1449
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1456 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid in
          if uu____1456
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
          let uu____1494 =
            FStar_List.fold_left
              (fun uu____1520 ->
                 fun u1 ->
                   match uu____1520 with
                   | (cur_kernel, cur_max, out) ->
                       let uu____1545 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1545 with
                        | (k_u, n) ->
                            let uu____1563 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1563
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1494 with
          | (uu____1584, u1, out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___153_1612 ->
                    match () with
                    | () ->
                        let uu____1615 =
                          let uu____1616 = FStar_List.nth env1 x in
                          FStar_Pervasives_Native.snd uu____1616 in
                        (match uu____1615 with
                         | Univ u3 ->
                             ((let uu____1635 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm") in
                               if uu____1635
                               then
                                 let uu____1640 =
                                   FStar_Syntax_Print.univ_to_string u3 in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1640
                               else ());
                              aux u3)
                         | Dummy -> [u2]
                         | uu____1645 ->
                             let uu____1646 =
                               let uu____1648 = FStar_Util.string_of_int x in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1648 in
                             failwith uu____1646)) ()
               with
               | uu____1658 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1664 =
                        let uu____1666 = FStar_Util.string_of_int x in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1666 in
                      failwith uu____1664))
          | FStar_Syntax_Syntax.U_unif uu____1671 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1682 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1693 -> [u2]
          | FStar_Syntax_Syntax.U_unknown -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1700 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1700 norm_univs_for_max in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest in
                   let uu____1717 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1717 with
                    | (FStar_Syntax_Syntax.U_zero, n) ->
                        let uu____1728 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3 ->
                                  let uu____1738 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1738 with
                                  | (uu____1745, m) -> n <= m)) in
                        if uu____1728 then rest1 else us1
                    | uu____1754 -> us1)
               | uu____1760 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1764 = aux u3 in
              FStar_List.map
                (fun uu____1767 -> FStar_Syntax_Syntax.U_succ uu____1767)
                uu____1764 in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1771 = aux u in
           match uu____1771 with
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
            (fun uu____1932 ->
               let uu____1933 = FStar_Syntax_Print.tag_of_term t in
               let uu____1935 = env_to_string env1 in
               let uu____1937 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print3 ">>> %s (env=%s)\nClosure_as_term %s\n"
                 uu____1933 uu____1935 uu____1937);
          (match env1 with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env1 stack1 t
           | uu____1950 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1953 ->
                    let uu____1968 = FStar_Syntax_Subst.compress t in
                    inline_closure_env cfg env1 stack1 uu____1968
                | FStar_Syntax_Syntax.Tm_unknown ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_constant uu____1969 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_name uu____1970 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_lazy uu____1971 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_fvar uu____1972 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1997 ->
                           let uu____2010 =
                             let uu____2012 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos in
                             let uu____2014 =
                               FStar_Syntax_Print.term_to_string t1 in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____2012 uu____2014 in
                           failwith uu____2010
                       | uu____2019 -> inline_closure_env cfg env1 stack1 t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1 ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_2055 ->
                                         match uu___4_2055 with
                                         | FStar_Syntax_Syntax.NT (x, t1) ->
                                             let uu____2062 =
                                               let uu____2069 =
                                                 inline_closure_env cfg env1
                                                   [] t1 in
                                               (x, uu____2069) in
                                             FStar_Syntax_Syntax.NT
                                               uu____2062
                                         | FStar_Syntax_Syntax.NM (x, i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___247_2081 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___247_2081.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___247_2081.FStar_Syntax_Syntax.sort)
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
                                              | uu____2087 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____2090 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes")))) in
                       let t1 =
                         let uu___256_2095 = t in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___256_2095.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___256_2095.FStar_Syntax_Syntax.vars)
                         } in
                       rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2116 =
                        let uu____2117 = norm_universe cfg env1 u in
                        FStar_Syntax_Syntax.Tm_type uu____2117 in
                      FStar_Syntax_Syntax.mk uu____2116
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
                    let t1 =
                      let uu____2125 =
                        FStar_List.map (norm_universe cfg env1) us in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2125 in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2127 = lookup_bvar env1 x in
                    (match uu____2127 with
                     | Univ uu____2130 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy ->
                         let x1 =
                           let uu___272_2135 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___272_2135.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___272_2135.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1
                     | Clos (env2, t0, uu____2141, uu____2142) ->
                         inline_closure_env cfg env2 stack1 t0)
                | FStar_Syntax_Syntax.Tm_app (head, args) ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____2233 ->
                              fun stack2 ->
                                match uu____2233 with
                                | (a, aq) ->
                                    let uu____2245 =
                                      let uu____2246 =
                                        let uu____2253 =
                                          let uu____2254 =
                                            let uu____2286 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu____2286, false) in
                                          Clos uu____2254 in
                                        (uu____2253, aq,
                                          (t.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____2246 in
                                    uu____2245 :: stack2) args) in
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
                    let uu____2454 = close_binders cfg env1 bs in
                    (match uu____2454 with
                     | (bs1, env') ->
                         let c1 = close_comp cfg env' c in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_refine (x, uu____2504) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env1 stack1
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
                    let uu____2515 =
                      let uu____2528 =
                        let uu____2537 = FStar_Syntax_Syntax.mk_binder x in
                        [uu____2537] in
                      close_binders cfg env1 uu____2528 in
                    (match uu____2515 with
                     | (x1, env2) ->
                         let phi1 = non_tail_inline_closure_env cfg env2 phi in
                         let t1 =
                           let uu____2582 =
                             let uu____2583 =
                               let uu____2590 =
                                 let uu____2591 = FStar_List.hd x1 in
                                 FStar_All.pipe_right uu____2591
                                   FStar_Pervasives_Native.fst in
                               (uu____2590, phi1) in
                             FStar_Syntax_Syntax.Tm_refine uu____2583 in
                           FStar_Syntax_Syntax.mk uu____2582
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env2 stack1 t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt)
                    ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2690 =
                            non_tail_inline_closure_env cfg env1 t2 in
                          FStar_Util.Inl uu____2690
                      | FStar_Util.Inr c ->
                          let uu____2704 = close_comp cfg env1 c in
                          FStar_Util.Inr uu____2704 in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env1) in
                    let t2 =
                      let uu____2723 =
                        let uu____2724 =
                          let uu____2751 =
                            non_tail_inline_closure_env cfg env1 t1 in
                          (uu____2751, (annot1, tacopt1), lopt) in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2724 in
                      FStar_Syntax_Syntax.mk uu____2723
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t2
                | FStar_Syntax_Syntax.Tm_quoted (t', qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic ->
                          let uu____2797 =
                            let uu____2798 =
                              let uu____2805 =
                                non_tail_inline_closure_env cfg env1 t' in
                              (uu____2805, qi) in
                            FStar_Syntax_Syntax.Tm_quoted uu____2798 in
                          FStar_Syntax_Syntax.mk uu____2797
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
                        (fun env2 -> fun uu____2860 -> dummy :: env2) env1
                        lb.FStar_Syntax_Syntax.lbunivs in
                    let typ =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let def =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbdef in
                    let uu____2881 =
                      let uu____2892 = FStar_Syntax_Syntax.is_top_level [lb] in
                      if uu____2892
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         let uu____2914 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body in
                         ((FStar_Util.Inl
                             (let uu___364_2930 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___364_2930.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___364_2930.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2914)) in
                    (match uu____2881 with
                     | (nm, body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs in
                         let lb1 =
                           let uu___370_2957 = lb in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___370_2957.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___370_2957.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___370_2957.FStar_Syntax_Syntax.lbpos)
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env0 stack1 t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2974, lbs), body) ->
                    let norm_one_lb env2 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____3040 -> fun env3 -> dummy :: env3)
                          lb.FStar_Syntax_Syntax.lbunivs env2 in
                      let env3 =
                        let uu____3057 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu____3057
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____3072 -> fun env3 -> dummy :: env3) lbs
                            env_univs in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp in
                      let nm =
                        let uu____3096 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu____3096
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           FStar_Util.Inl
                             (let uu___393_3107 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___393_3107.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___393_3107.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              })) in
                      let uu___396_3108 = lb in
                      let uu____3109 =
                        non_tail_inline_closure_env cfg env3
                          lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___396_3108.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___396_3108.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3109;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___396_3108.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___396_3108.FStar_Syntax_Syntax.lbpos)
                      } in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env1)) in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3141 -> fun env2 -> dummy :: env2) lbs1
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
            (fun uu____3233 ->
               let uu____3234 = FStar_Syntax_Print.tag_of_term t in
               let uu____3236 = env_to_string env1 in
               let uu____3238 = stack_to_string stack1 in
               let uu____3240 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu____3234 uu____3236 uu____3238 uu____3240);
          (match stack1 with
           | [] -> t
           | (Arg
               (Clos (env_arg, tm, uu____3247, uu____3248), aq, r))::stack2
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
               let uu____3339 = close_binders cfg env' bs in
               (match uu____3339 with
                | (bs1, uu____3355) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt in
                    let uu____3375 =
                      let uu___463_3378 = FStar_Syntax_Util.abs bs1 t lopt1 in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___463_3378.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___463_3378.FStar_Syntax_Syntax.vars)
                      } in
                    rebuild_closure cfg env1 stack2 uu____3375)
           | (Match (env2, branches1, cfg1, r))::stack2 ->
               let close_one_branch env3 uu____3434 =
                 match uu____3434 with
                 | (pat, w_opt, tm) ->
                     let rec norm_pat env4 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3549 ->
                           (p, env4)
                       | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                           let uu____3580 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3669 ->
                                     fun uu____3670 ->
                                       match (uu____3669, uu____3670) with
                                       | ((pats1, env5), (p1, b)) ->
                                           let uu____3820 = norm_pat env5 p1 in
                                           (match uu____3820 with
                                            | (p2, env6) ->
                                                (((p2, b) :: pats1), env6)))
                                  ([], env4)) in
                           (match uu____3580 with
                            | (pats1, env5) ->
                                ((let uu___500_3990 = p in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___500_3990.FStar_Syntax_Syntax.p)
                                  }), env5))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___504_4011 = x in
                             let uu____4012 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___504_4011.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___504_4011.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4012
                             } in
                           ((let uu___507_4026 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___507_4026.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___511_4037 = x in
                             let uu____4038 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___511_4037.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___511_4037.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4038
                             } in
                           ((let uu___514_4052 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___514_4052.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_dot_term (x, t1) ->
                           let x1 =
                             let uu___520_4068 = x in
                             let uu____4069 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___520_4068.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___520_4068.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4069
                             } in
                           let t2 = non_tail_inline_closure_env cfg1 env4 t1 in
                           ((let uu___524_4086 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___524_4086.FStar_Syntax_Syntax.p)
                             }), env4) in
                     let uu____4091 = norm_pat env3 pat in
                     (match uu____4091 with
                      | (pat1, env4) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4160 =
                                  non_tail_inline_closure_env cfg1 env4 w in
                                FStar_Pervasives_Native.Some uu____4160 in
                          let tm1 = non_tail_inline_closure_env cfg1 env4 tm in
                          (pat1, w_opt1, tm1)) in
               let t1 =
                 let uu____4179 =
                   let uu____4180 =
                     let uu____4203 =
                       FStar_All.pipe_right branches1
                         (FStar_List.map (close_one_branch env2)) in
                     (t, uu____4203) in
                   FStar_Syntax_Syntax.Tm_match uu____4180 in
                 FStar_Syntax_Syntax.mk uu____4179 t.FStar_Syntax_Syntax.pos in
               rebuild_closure cfg1 env2 stack2 t1
           | (Meta (env_m, m, r))::stack2 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
                     let uu____4339 =
                       let uu____4360 =
                         FStar_All.pipe_right names
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m)) in
                       let uu____4377 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1 ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4486 ->
                                         match uu____4486 with
                                         | (a, q) ->
                                             let uu____4513 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a in
                                             (uu____4513, q))))) in
                       (uu____4360, uu____4377) in
                     FStar_Syntax_Syntax.Meta_pattern uu____4339
                 | FStar_Syntax_Syntax.Meta_monadic (m1, tbody) ->
                     let uu____4542 =
                       let uu____4549 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m1, uu____4549) in
                     FStar_Syntax_Syntax.Meta_monadic uu____4542
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) ->
                     let uu____4561 =
                       let uu____4570 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m1, m2, uu____4570) in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4561
                 | uu____4575 -> m in
               let t1 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (t, m1))
                   r in
               rebuild_closure cfg env1 stack2 t1
           | uu____4581 -> failwith "Impossible: unexpected stack element")
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
            let uu____4597 =
              let uu____4598 =
                let uu____4599 = inline_closure_env cfg env1 [] t in
                FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____4599 in
              FStar_Syntax_Syntax.Meta uu____4598 in
            FStar_Pervasives_Native.Some uu____4597
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
            let uu____4605 =
              let uu____4606 =
                let uu____4607 = inline_closure_env cfg env1 [] t in
                FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____4607 in
              FStar_Syntax_Syntax.Meta uu____4606 in
            FStar_Pervasives_Native.Some uu____4605
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
        let uu____4624 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4708 ->
                  fun uu____4709 ->
                    match (uu____4708, uu____4709) with
                    | ((env2, out), (b, imp)) ->
                        let b1 =
                          let uu___584_4849 = b in
                          let uu____4850 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___584_4849.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___584_4849.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4850
                          } in
                        let imp1 = close_imp cfg env2 imp in
                        let env3 = dummy :: env2 in
                        (env3, ((b1, imp1) :: out))) (env1, [])) in
        match uu____4624 with | (env2, bs1) -> ((FStar_List.rev bs1), env2)
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
        | uu____4992 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t, uopt) ->
                 let uu____5005 = inline_closure_env cfg env1 [] t in
                 let uu____5006 =
                   FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____5005 uu____5006
             | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                 let uu____5019 = inline_closure_env cfg env1 [] t in
                 let uu____5020 =
                   FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5019 uu____5020
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5074 ->
                           match uu____5074 with
                           | (a, q) ->
                               let uu____5095 =
                                 inline_closure_env cfg env1 [] a in
                               (uu____5095, q))) in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5112 ->
                           match uu___5_5112 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5116 =
                                 inline_closure_env cfg env1 [] t in
                               FStar_Syntax_Syntax.DECREASES uu____5116
                           | f -> f)) in
                 let uu____5120 =
                   let uu___617_5121 = c1 in
                   let uu____5122 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5122;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___617_5121.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____5120)
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
                   (fun uu___6_5140 ->
                      match uu___6_5140 with
                      | FStar_Syntax_Syntax.DECREASES uu____5142 -> false
                      | uu____5146 -> true)) in
            let rc1 =
              let uu___629_5149 = rc in
              let uu____5150 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___629_5149.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5150;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____5159 -> lopt
let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5180 ->
            match uu___7_5180 with
            | FStar_Syntax_Syntax.DECREASES uu____5182 -> false
            | uu____5186 -> true))
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
    let uu____5233 = FStar_ST.op_Bang unembed_binder_knot in
    match uu____5233 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5272 = FStar_Syntax_Embeddings.unembed e t in
        uu____5272 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
let mk_psc_subst :
  'uuuuuu5292 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'uuuuuu5292) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg ->
    fun env1 ->
      FStar_List.fold_right
        (fun uu____5354 ->
           fun subst ->
             match uu____5354 with
             | (binder_opt, closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b, Clos
                     (env2, term, uu____5395, uu____5396)) ->
                      let uu____5457 = b in
                      (match uu____5457 with
                       | (bv, uu____5465) ->
                           let uu____5466 =
                             let uu____5468 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid in
                             Prims.op_Negation uu____5468 in
                           if uu____5466
                           then subst
                           else
                             (let term1 = closure_as_term cfg env2 term in
                              let uu____5476 = unembed_binder term1 in
                              match uu____5476 with
                              | FStar_Pervasives_Native.None -> subst
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5483 =
                                      let uu___669_5484 = bv in
                                      let uu____5485 =
                                        FStar_Syntax_Subst.subst subst
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___669_5484.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___669_5484.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5485
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____5483 in
                                  let b_for_x =
                                    let uu____5491 =
                                      let uu____5498 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5498) in
                                    FStar_Syntax_Syntax.NT uu____5491 in
                                  let subst1 =
                                    FStar_List.filter
                                      (fun uu___8_5514 ->
                                         match uu___8_5514 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5516,
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  b';
                                                FStar_Syntax_Syntax.pos =
                                                  uu____5518;
                                                FStar_Syntax_Syntax.vars =
                                                  uu____5519;_})
                                             ->
                                             let uu____5524 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname in
                                             Prims.op_Negation uu____5524
                                         | uu____5526 -> true) subst in
                                  b_for_x :: subst1))
                  | uu____5528 -> subst)) env1 []
let reduce_primops :
  'uuuuuu5550 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5550)
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
            (let uu____5602 = FStar_Syntax_Util.head_and_args tm in
             match uu____5602 with
             | (head, args) ->
                 let uu____5647 =
                   let uu____5648 = FStar_Syntax_Util.un_uinst head in
                   uu____5648.FStar_Syntax_Syntax.n in
                 (match uu____5647 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5654 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                      (match uu____5654 with
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
                                (fun uu____5677 ->
                                   let uu____5678 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name in
                                   let uu____5680 =
                                     FStar_Util.string_of_int l in
                                   let uu____5682 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5678 uu____5680 uu____5682);
                              tm)
                           else
                             (let uu____5687 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args in
                              match uu____5687 with
                              | (args_1, args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5773 ->
                                        let uu____5774 =
                                          FStar_Syntax_Print.term_to_string
                                            tm in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5774);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5779 ->
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
                                           (fun uu____5793 ->
                                              let uu____5794 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5794);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5802 ->
                                              let uu____5803 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              let uu____5805 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5803 uu____5805);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5808 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5812 ->
                                 let uu____5813 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5813);
                            tm)
                       | FStar_Pervasives_Native.None -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5819 ->
                            let uu____5820 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5820);
                       (match args with
                        | (a1, uu____5826)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5851 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5865 ->
                            let uu____5866 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5866);
                       (match args with
                        | (t, uu____5872)::(r, uu____5874)::[] ->
                            let uu____5915 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r in
                            (match uu____5915 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None -> tm)
                        | uu____5921 -> tm))
                  | uu____5932 -> tm))
let reduce_equality :
  'uuuuuu5943 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5943)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb ->
    fun cfg ->
      fun tm ->
        reduce_primops norm_cb
          (let uu___757_5992 = cfg in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___759_5995 = FStar_TypeChecker_Cfg.default_steps in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___759_5995.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___759_5995.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___759_5995.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___759_5995.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___759_5995.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___759_5995.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___759_5995.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___759_5995.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___759_5995.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___759_5995.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___759_5995.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___759_5995.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___759_5995.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___759_5995.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___759_5995.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___759_5995.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___759_5995.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___759_5995.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___759_5995.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___759_5995.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___759_5995.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___759_5995.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___759_5995.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___759_5995.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___759_5995.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___759_5995.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___757_5992.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___757_5992.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___757_5992.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___757_5992.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___757_5992.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___757_5992.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___757_5992.FStar_TypeChecker_Cfg.reifying)
           }) tm
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_none -> true | uu____6006 -> false
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_ready -> true | uu____6017 -> false
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Norm_request_requires_rejig -> true
    | uu____6028 -> false
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd ->
    fun args ->
      let aux min_args =
        let uu____6049 = FStar_All.pipe_right args FStar_List.length in
        FStar_All.pipe_right uu____6049
          (fun n ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig) in
      let uu____6081 =
        let uu____6082 = FStar_Syntax_Util.un_uinst hd in
        uu____6082.FStar_Syntax_Syntax.n in
      match uu____6081 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____6091 -> Norm_request_none
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6100 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid in
       Prims.op_Negation uu____6100)
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd ->
    fun args ->
      let uu____6113 =
        let uu____6114 = FStar_Syntax_Util.un_uinst hd in
        uu____6114.FStar_Syntax_Syntax.n in
      match uu____6113 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6172 = FStar_Syntax_Util.mk_app hd [t1; t2] in
               FStar_Syntax_Util.mk_app uu____6172 rest
           | uu____6199 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6239 = FStar_Syntax_Util.mk_app hd [t] in
               FStar_Syntax_Util.mk_app uu____6239 rest
           | uu____6258 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6332 = FStar_Syntax_Util.mk_app hd [t1; t2; t3] in
               FStar_Syntax_Util.mk_app uu____6332 rest
           | uu____6367 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6369 ->
          let uu____6370 =
            let uu____6372 = FStar_Syntax_Print.term_to_string hd in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6372 in
          failwith uu____6370
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6393 ->
    match uu___9_6393 with
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
        let uu____6400 =
          let uu____6403 =
            let uu____6404 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldOnly uu____6404 in
          [uu____6403] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6400
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____6412 =
          let uu____6415 =
            let uu____6416 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldFully uu____6416 in
          [uu____6415] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6412
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____6424 =
          let uu____6427 =
            let uu____6428 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldAttr uu____6428 in
          [uu____6427] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6424
    | FStar_Syntax_Embeddings.NBE -> [FStar_TypeChecker_Env.NBE]
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s ->
    let s1 = FStar_List.concatMap tr_norm_step s in
    let add_exclude s2 z =
      let uu____6464 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2 in
      if uu____6464 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2 in
    let s2 = FStar_TypeChecker_Env.Beta :: s1 in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota in s4
let get_norm_request :
  'uuuuuu6489 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu6489) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun full_norm ->
      fun args ->
        let parse_steps s =
          let uu____6540 =
            let uu____6545 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6545 s in
          match uu____6540 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6561 = tr_norm_steps steps in
              FStar_Pervasives_Native.Some uu____6561
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
        | uu____6596::(tm, uu____6598)::[] ->
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
        | (tm, uu____6627)::[] ->
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
        | (steps, uu____6648)::uu____6649::(tm, uu____6651)::[] ->
            let uu____6672 =
              let uu____6677 = full_norm steps in parse_steps uu____6677 in
            (match uu____6672 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6707 -> FStar_Pervasives_Native.None
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun s ->
      fun tm ->
        let delta_level =
          let uu____6739 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6746 ->
                    match uu___10_6746 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6748 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6750 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6754 -> true
                    | uu____6758 -> false)) in
          if uu____6739
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta] in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6768 ->
             let uu____6769 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6769);
        (let tm_norm =
           let uu____6773 =
             let uu____6788 = FStar_TypeChecker_Cfg.cfg_env cfg in
             uu____6788.FStar_TypeChecker_Env.nbe in
           uu____6773 s cfg.FStar_TypeChecker_Cfg.tcenv tm in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6792 ->
              let uu____6793 = FStar_Syntax_Print.term_to_string tm_norm in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6793);
         tm_norm)
let firstn :
  'uuuuuu6803 .
    Prims.int ->
      'uuuuuu6803 Prims.list ->
        ('uuuuuu6803 Prims.list * 'uuuuuu6803 Prims.list)
  =
  fun k ->
    fun l ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg ->
    fun stack1 ->
      let rec drop_irrel uu___11_6860 =
        match uu___11_6860 with
        | (MemoLazy uu____6865)::s -> drop_irrel s
        | (UnivArgs uu____6875)::s -> drop_irrel s
        | s -> s in
      let uu____6888 = drop_irrel stack1 in
      match uu____6888 with
      | (App
          (uu____6892,
           {
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify);
             FStar_Syntax_Syntax.pos = uu____6893;
             FStar_Syntax_Syntax.vars = uu____6894;_},
           uu____6895, uu____6896))::uu____6897
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6902 -> false
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t, uu____6931) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t, uu____6941) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6962 ->
                  match uu____6962 with
                  | (a, uu____6973) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args) in
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6984 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____7001 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____7003 -> false
    | FStar_Syntax_Syntax.Tm_type uu____7017 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____7019 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____7021 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____7023 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____7025 -> false
    | FStar_Syntax_Syntax.Tm_unknown -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____7028 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____7036 -> false
    | FStar_Syntax_Syntax.Tm_let uu____7044 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____7059 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7079 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7095 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7103 -> true
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7175 ->
                   match uu____7175 with
                   | (a, uu____7186) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____7197) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7296, args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7351 ->
                        match uu____7351 with
                        | (a, uu____7362) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7371, uu____7372, t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7378, t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7384 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7394 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7396 -> false))
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_no -> true | uu____7407 -> false
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_yes -> true | uu____7418 -> false
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_fully -> true | uu____7429 -> false
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_reify -> true | uu____7440 -> false
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
            let uu____7473 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
            match uu____7473 with
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
              (fun uu____7672 ->
                 fun uu____7673 ->
                   match (uu____7672, uu____7673) with
                   | ((a, b, c), (x, y, z)) -> ((a || x), (b || y), (c || z)))
              l (false, false, false) in
          let string_of_res uu____7779 =
            match uu____7779 with
            | (x, y, z) ->
                let uu____7799 = FStar_Util.string_of_bool x in
                let uu____7801 = FStar_Util.string_of_bool y in
                let uu____7803 = FStar_Util.string_of_bool z in
                FStar_Util.format3 "(%s,%s,%s)" uu____7799 uu____7801
                  uu____7803 in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7831 ->
                    let uu____7832 = FStar_Syntax_Print.fv_to_string fv in
                    let uu____7834 = FStar_Util.string_of_bool b in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7832 uu____7834);
               if b then reif else no)
            else
              if
                (let uu____7849 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                 FStar_Option.isSome uu____7849)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7854 ->
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
                          ((is_rec, uu____7889), uu____7890);
                        FStar_Syntax_Syntax.sigrng = uu____7891;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7893;
                        FStar_Syntax_Syntax.sigattrs = uu____7894;
                        FStar_Syntax_Syntax.sigopts = uu____7895;_},
                      uu____7896),
                     uu____7897),
                    uu____7898, uu____7899, uu____7900) when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8009 ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____8011, uu____8012, uu____8013, uu____8014) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8081 ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec, uu____8084), uu____8085);
                        FStar_Syntax_Syntax.sigrng = uu____8086;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8088;
                        FStar_Syntax_Syntax.sigattrs = uu____8089;
                        FStar_Syntax_Syntax.sigopts = uu____8090;_},
                      uu____8091),
                     uu____8092),
                    uu____8093, uu____8094, uu____8095) when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8204 ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8206, FStar_Pervasives_Native.Some uu____8207,
                    uu____8208, uu____8209) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8277 ->
                           let uu____8278 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8278);
                      (let uu____8281 =
                         let uu____8293 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8319 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____8319 in
                         let uu____8331 =
                           let uu____8343 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8369 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8369 in
                           let uu____8385 =
                             let uu____8397 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8423 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8423 in
                             [uu____8397] in
                           uu____8343 :: uu____8385 in
                         uu____8293 :: uu____8331 in
                       comb_or uu____8281))
                 | (uu____8471, uu____8472, FStar_Pervasives_Native.Some
                    uu____8473, uu____8474) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8542 ->
                           let uu____8543 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8543);
                      (let uu____8546 =
                         let uu____8558 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8584 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____8584 in
                         let uu____8596 =
                           let uu____8608 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8634 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8634 in
                           let uu____8650 =
                             let uu____8662 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8688 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8688 in
                             [uu____8662] in
                           uu____8608 :: uu____8650 in
                         uu____8558 :: uu____8596 in
                       comb_or uu____8546))
                 | (uu____8736, uu____8737, uu____8738,
                    FStar_Pervasives_Native.Some uu____8739) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8807 ->
                           let uu____8808 =
                             FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8808);
                      (let uu____8811 =
                         let uu____8823 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8849 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids in
                               FStar_All.pipe_left yesno uu____8849 in
                         let uu____8861 =
                           let uu____8873 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8899 =
                                   FStar_Util.for_some
                                     (fun at ->
                                        FStar_Util.for_some
                                          (fun lid ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs in
                                 FStar_All.pipe_left yesno uu____8899 in
                           let uu____8915 =
                             let uu____8927 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8953 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left fullyno uu____8953 in
                             [uu____8927] in
                           uu____8873 :: uu____8915 in
                         uu____8823 :: uu____8861 in
                       comb_or uu____8811))
                 | uu____9001 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____9047 ->
                           let uu____9048 =
                             FStar_Syntax_Print.fv_to_string fv in
                           let uu____9050 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta in
                           let uu____9052 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____9048 uu____9050 uu____9052);
                      (let uu____9055 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_9061 ->
                                 match uu___12_9061 with
                                 | FStar_TypeChecker_Env.NoDelta -> false
                                 | FStar_TypeChecker_Env.InliningDelta ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                     -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____9067 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____9067 l)) in
                       FStar_All.pipe_left yesno uu____9055))) in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9083 ->
               let uu____9084 = FStar_Syntax_Print.fv_to_string fv in
               let uu____9086 =
                 let uu____9088 = FStar_Syntax_Syntax.range_of_fv fv in
                 FStar_Range.string_of_range uu____9088 in
               let uu____9089 = string_of_res res in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9084 uu____9086 uu____9089);
          (match res with
           | (false, uu____9092, uu____9093) -> Should_unfold_no
           | (true, false, false) -> Should_unfold_yes
           | (true, true, false) -> Should_unfold_fully
           | (true, false, true) -> Should_unfold_reify
           | uu____9118 ->
               let uu____9128 =
                 let uu____9130 = string_of_res res in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9130 in
               FStar_All.pipe_left failwith uu____9128)
let decide_unfolding :
  'uuuuuu9149 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu9149 ->
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
                    let uu___1168_9218 = cfg in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1170_9221 = cfg.FStar_TypeChecker_Cfg.steps in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1170_9221.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1170_9221.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1168_9218.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9283 = push e t in (UnivArgs (us, r)) ::
                          uu____9283
                    | h::t -> e :: h :: t in
                  let ref =
                    let uu____9295 =
                      let uu____9296 =
                        let uu____9297 = FStar_Syntax_Syntax.lid_of_fv fv in
                        FStar_Const.Const_reflect uu____9297 in
                      FStar_Syntax_Syntax.Tm_constant uu____9296 in
                    FStar_Syntax_Syntax.mk uu____9295 FStar_Range.dummyRange in
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
    let uu____9363 =
      let uu____9364 = FStar_Syntax_Subst.compress t in
      uu____9364.FStar_Syntax_Syntax.n in
    match uu____9363 with
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu____9395 =
          let uu____9396 = FStar_Syntax_Util.un_uinst hd in
          uu____9396.FStar_Syntax_Syntax.n in
        (match uu____9395 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9413 =
                 let uu____9420 =
                   let uu____9431 = FStar_All.pipe_right args FStar_List.tl in
                   FStar_All.pipe_right uu____9431 FStar_List.tl in
                 FStar_All.pipe_right uu____9420 FStar_List.hd in
               FStar_All.pipe_right uu____9413 FStar_Pervasives_Native.fst in
             FStar_Pervasives_Native.Some f
         | uu____9530 -> FStar_Pervasives_Native.None)
    | uu____9531 -> FStar_Pervasives_Native.None
let (is_partial_primop_app :
  FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun cfg ->
    fun t ->
      let uu____9545 = FStar_Syntax_Util.head_and_args t in
      match uu____9545 with
      | (hd, args) ->
          let uu____9589 =
            let uu____9590 = FStar_Syntax_Util.un_uinst hd in
            uu____9590.FStar_Syntax_Syntax.n in
          (match uu____9589 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____9595 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
               (match uu____9595 with
                | FStar_Pervasives_Native.Some prim_step ->
                    prim_step.FStar_TypeChecker_Cfg.arity >
                      (FStar_List.length args)
                | FStar_Pervasives_Native.None -> false)
           | uu____9609 -> false)
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9889 ->
                   let uu____9904 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9904
               | uu____9907 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9917 ->
               let uu____9918 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____9920 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm in
               let uu____9922 = FStar_Syntax_Print.term_to_string t1 in
               let uu____9924 =
                 FStar_Util.string_of_int (FStar_List.length env1) in
               let uu____9932 =
                 let uu____9934 =
                   let uu____9937 = firstn (Prims.of_int (4)) stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9937 in
                 stack_to_string uu____9934 in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9918 uu____9920 uu____9922 uu____9924 uu____9932);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9965 ->
               let uu____9966 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9966);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9972 ->
                     let uu____9973 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9973);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9976 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9980 ->
                     let uu____9981 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9981);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____9984 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9988 ->
                     let uu____9989 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9989);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9992 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9996 ->
                     let uu____9997 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9997);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10000;
                 FStar_Syntax_Syntax.fv_delta = uu____10001;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10005 ->
                     let uu____10006 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10006);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10009;
                 FStar_Syntax_Syntax.fv_delta = uu____10010;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10011);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10021 ->
                     let uu____10022 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10022);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid in
               let uu____10028 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo in
               (match uu____10028 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____10031)
                    when uu____10031 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____10035 ->
                          let uu____10036 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____10036);
                     rebuild cfg env1 stack1 t1)
                | uu____10039 ->
                    let uu____10042 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo in
                    (match uu____10042 with
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
               let uu____10081 = closure_as_term cfg env1 t2 in
               rebuild cfg env1 stack1 uu____10081
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10109 = is_norm_request hd args in
                  uu____10109 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10115 = rejig_norm_request hd args in
                 norm cfg env1 stack1 uu____10115))
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10143 = is_norm_request hd args in
                  uu____10143 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1292_10150 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1294_10153 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1294_10153.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1292_10150.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1292_10150.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1292_10150.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1292_10150.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1292_10150.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1292_10150.FStar_TypeChecker_Cfg.reifying)
                   } in
                 let uu____10160 =
                   get_norm_request cfg (norm cfg' env1 []) args in
                 match uu____10160 with
                 | FStar_Pervasives_Native.None ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____10196 ->
                                 fun stack2 ->
                                   match uu____10196 with
                                   | (a, aq) ->
                                       let uu____10208 =
                                         let uu____10209 =
                                           let uu____10216 =
                                             let uu____10217 =
                                               let uu____10249 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None in
                                               (env1, a, uu____10249, false) in
                                             Clos uu____10217 in
                                           (uu____10216, aq,
                                             (t1.FStar_Syntax_Syntax.pos)) in
                                         Arg uu____10209 in
                                       uu____10208 :: stack2) args) in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10317 ->
                            let uu____10318 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10318);
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
                         let uu____10350 =
                           let uu____10352 =
                             let uu____10354 = FStar_Util.time_diff start fin in
                             FStar_Pervasives_Native.snd uu____10354 in
                           FStar_Util.string_of_int uu____10352 in
                         let uu____10361 =
                           FStar_Syntax_Print.term_to_string tm' in
                         let uu____10363 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1 in
                         let uu____10365 =
                           FStar_Syntax_Print.term_to_string tm_norm in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10350 uu____10361 uu____10363 uu____10365)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s, tm) ->
                     let delta_level =
                       let uu____10385 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10392 ->
                                 match uu___13_10392 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10394 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10396 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10400 -> true
                                 | uu____10404 -> false)) in
                       if uu____10385
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta] in
                     let cfg'1 =
                       let uu___1332_10412 = cfg in
                       let uu____10413 =
                         let uu___1334_10414 =
                           FStar_TypeChecker_Cfg.to_fsteps s in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1334_10414.FStar_TypeChecker_Cfg.for_extraction)
                         } in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10413;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1332_10412.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1332_10412.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1332_10412.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1332_10412.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1332_10412.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1332_10412.FStar_TypeChecker_Cfg.reifying)
                       } in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1 in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10422 =
                           let uu____10423 =
                             let uu____10428 = FStar_Util.now () in
                             (tm, uu____10428) in
                           Debug uu____10423 in
                         uu____10422 :: tail
                       else tail in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u in
               let uu____10433 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____10433
           | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____10444 =
                      let uu____10451 =
                        FStar_List.map (norm_universe cfg env1) us in
                      (uu____10451, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____10444 in
                  let stack2 = us1 :: stack1 in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10460 = lookup_bvar env1 x in
               (match uu____10460 with
                | Univ uu____10461 ->
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
                      let uu____10515 = FStar_ST.op_Bang r in
                      (match uu____10515 with
                       | FStar_Pervasives_Native.Some (env3, t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10611 ->
                                 let uu____10612 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____10614 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10612
                                   uu____10614);
                            (let uu____10617 = maybe_weakly_reduced t' in
                             if uu____10617
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____10620 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
               (match stack1 with
                | (UnivArgs uu____10664)::uu____10665 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c, uu____10676, uu____10677))::stack_rest ->
                    (match c with
                     | Univ uu____10681 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____10690 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10720 ->
                                    let uu____10721 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10721);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10757 ->
                                    let uu____10758 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10758);
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
                       (fun uu____10806 ->
                          let uu____10807 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10807);
                     norm cfg env1 stack2 t1)
                | (Match uu____10810)::uu____10811 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10826 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10826 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10862 -> dummy :: env2) env1) in
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
                                          let uu____10906 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____10906)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10914 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10914.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10914.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10915 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10921 ->
                                 let uu____10922 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10922);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_10937 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_10937.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____10941)::uu____10942 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10953 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____10953 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____10989 -> dummy :: env2) env1) in
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
                                          let uu____11033 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11033)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11041 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11041.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11041.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11042 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11048 ->
                                 let uu____11049 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11049);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11064 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11064.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11068)::uu____11069 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11082 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11082 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11118 -> dummy :: env2) env1) in
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
                                          let uu____11162 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11162)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11170 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11170.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11170.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11171 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11177 ->
                                 let uu____11178 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11178);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11193 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11193.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11197)::uu____11198 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11213 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11213 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11249 -> dummy :: env2) env1) in
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
                                          let uu____11293 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11293)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11301 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11301.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11301.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11302 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11308 ->
                                 let uu____11309 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11309);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11324 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11324.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11328)::uu____11329 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11344 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11344 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11380 -> dummy :: env2) env1) in
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
                                          let uu____11424 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11424)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11432 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11432.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11432.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11433 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11439 ->
                                 let uu____11440 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11440);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11455 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11455.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____11459)::uu____11460 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11475 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11475 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11511 -> dummy :: env2) env1) in
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
                                          let uu____11555 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11555)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11563 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11563.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11563.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11564 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11570 ->
                                 let uu____11571 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11571);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11586 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11586.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11590)::uu____11591 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11610 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11610 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11646 -> dummy :: env2) env1) in
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
                                          let uu____11690 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11690)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11698 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11698.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11698.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11699 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11705 ->
                                 let uu____11706 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11706);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11721 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11721.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11729 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11729 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 ->
                                     fun uu____11765 -> dummy :: env2) env1) in
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
                                          let uu____11809 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11809)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11817 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11817.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11817.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11818 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11824 ->
                                 let uu____11825 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11825);
                            (let stack2 = (Cfg cfg) :: stack1 in
                             let cfg1 =
                               let uu___1463_11840 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1463_11840.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head, args) ->
               let strict_args =
                 let uu____11876 =
                   let uu____11877 = FStar_Syntax_Util.un_uinst head in
                   uu____11877.FStar_Syntax_Syntax.n in
                 match uu____11876 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11886 -> FStar_Pervasives_Native.None in
               (match strict_args with
                | FStar_Pervasives_Native.None ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____11907 ->
                              fun stack2 ->
                                match uu____11907 with
                                | (a, aq) ->
                                    let uu____11919 =
                                      let uu____11920 =
                                        let uu____11927 =
                                          let uu____11928 =
                                            let uu____11960 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu____11960, false) in
                                          Clos uu____11928 in
                                        (uu____11927, aq,
                                          (t1.FStar_Syntax_Syntax.pos)) in
                                      Arg uu____11920 in
                                    uu____11919 :: stack2) args) in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12028 ->
                          let uu____12029 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args) in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12029);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12080 ->
                              match uu____12080 with
                              | (a, i) ->
                                  let uu____12091 = norm cfg env1 [] a in
                                  (uu____12091, i))) in
                    let norm_args_len = FStar_List.length norm_args in
                    let uu____12097 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12112 = FStar_List.nth norm_args i in
                                 match uu____12112 with
                                 | (arg_i, uu____12123) ->
                                     let uu____12124 =
                                       FStar_Syntax_Util.head_and_args arg_i in
                                     (match uu____12124 with
                                      | (head1, uu____12143) ->
                                          let uu____12168 =
                                            let uu____12169 =
                                              FStar_Syntax_Util.un_uinst
                                                head1 in
                                            uu____12169.FStar_Syntax_Syntax.n in
                                          (match uu____12168 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12173 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12176 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12176
                                           | uu____12177 -> false))))) in
                    if uu____12097
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____12194 ->
                                fun stack2 ->
                                  match uu____12194 with
                                  | (a, aq) ->
                                      let uu____12206 =
                                        let uu____12207 =
                                          let uu____12214 =
                                            let uu____12215 =
                                              let uu____12247 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a)) in
                                              (env1, a, uu____12247, false) in
                                            Clos uu____12215 in
                                          (uu____12214, aq,
                                            (t1.FStar_Syntax_Syntax.pos)) in
                                        Arg uu____12207 in
                                      uu____12206 :: stack2) norm_args) in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12329 ->
                            let uu____12330 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12330);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x, uu____12348) when
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
                             ((let uu___1525_12393 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1525_12393.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1525_12393.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2
                  | uu____12394 ->
                      let uu____12409 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 uu____12409)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
                  let uu____12413 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12413 with
                  | (closing, f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1 in
                      let t2 =
                        let uu____12444 =
                          let uu____12445 =
                            let uu____12452 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___1534_12458 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1534_12458.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1534_12458.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12452) in
                          FStar_Syntax_Syntax.Tm_refine uu____12445 in
                        FStar_Syntax_Syntax.mk uu____12444
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12482 = closure_as_term cfg env1 t1 in
                 rebuild cfg env1 stack1 uu____12482
               else
                 (let uu____12485 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12485 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu____12493 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2 -> fun uu____12519 -> dummy :: env2)
                               env1) in
                        norm_comp cfg uu____12493 c1 in
                      let t2 =
                        let uu____12543 = norm_binders cfg env1 bs1 in
                        FStar_Syntax_Util.arrow uu____12543 c2 in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) ->
               (match stack1 with
                | (Match uu____12656)::uu____12657 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12670 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____12672)::uu____12673 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12684 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____12686,
                     {
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify);
                       FStar_Syntax_Syntax.pos = uu____12687;
                       FStar_Syntax_Syntax.vars = uu____12688;_},
                     uu____12689, uu____12690))::uu____12691
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12698 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____12700)::uu____12701 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12712 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____12714 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12717 ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11 in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12722 ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12748 = norm cfg env1 [] t2 in
                             FStar_Util.Inl uu____12748
                         | FStar_Util.Inr c ->
                             let uu____12762 = norm_comp cfg env1 c in
                             FStar_Util.Inr uu____12762 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 []) in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____12785 =
                               let uu____12786 =
                                 let uu____12813 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____12813, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12786 in
                             FStar_Syntax_Syntax.mk uu____12785
                               t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env1 stack2 t2
                       | uu____12848 ->
                           let uu____12849 =
                             let uu____12850 =
                               let uu____12851 =
                                 let uu____12878 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____12878, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12851 in
                             FStar_Syntax_Syntax.mk uu____12850
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env1 stack1 uu____12849))))
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
                   let uu___1613_12956 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1615_12959 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1615_12959.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1613_12956.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____13000 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13000 with
                         | (openings, lbunivs) ->
                             let cfg1 =
                               let uu___1628_13020 = cfg in
                               let uu____13021 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____13021;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1628_13020.FStar_TypeChecker_Cfg.reifying)
                               } in
                             let norm1 t2 =
                               let uu____13028 =
                                 let uu____13029 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env1 [] uu____13029 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13028 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___1635_13032 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1635_13032.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1635_13032.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1635_13032.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1635_13032.FStar_Syntax_Syntax.lbpos)
                             })) in
               let uu____13033 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu____13033
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13046,
                 { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____13047;
                   FStar_Syntax_Syntax.lbunivs = uu____13048;
                   FStar_Syntax_Syntax.lbtyp = uu____13049;
                   FStar_Syntax_Syntax.lbeff = uu____13050;
                   FStar_Syntax_Syntax.lbdef = uu____13051;
                   FStar_Syntax_Syntax.lbattrs = uu____13052;
                   FStar_Syntax_Syntax.lbpos = uu____13053;_}::uu____13054),
                uu____13055)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
               let uu____13100 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb in
               if uu____13100
               then
                 let binder =
                   let uu____13104 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13104 in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef in
                 let env2 =
                   let uu____13115 =
                     let uu____13122 =
                       let uu____13123 =
                         let uu____13155 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env1, def, uu____13155, false) in
                       Clos uu____13123 in
                     ((FStar_Pervasives_Native.Some binder), uu____13122) in
                   uu____13115 :: env1 in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13230 ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____13234 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13237 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff in
                       FStar_Syntax_Util.is_div_effect uu____13237) in
                  if uu____13234
                  then
                    let ffun =
                      let uu____13242 =
                        let uu____13243 =
                          let uu____13262 =
                            let uu____13271 =
                              let uu____13278 =
                                FStar_All.pipe_right
                                  lb.FStar_Syntax_Syntax.lbname
                                  FStar_Util.left in
                              FStar_Syntax_Syntax.mk_binder uu____13278 in
                            [uu____13271] in
                          (uu____13262, body, FStar_Pervasives_Native.None) in
                        FStar_Syntax_Syntax.Tm_abs uu____13243 in
                      FStar_Syntax_Syntax.mk uu____13242
                        t1.FStar_Syntax_Syntax.pos in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13312 ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13319 ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13321 = closure_as_term cfg env1 t1 in
                        rebuild cfg env1 stack1 uu____13321))
                    else
                      (let uu____13324 =
                         let uu____13329 =
                           let uu____13330 =
                             let uu____13337 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left in
                             FStar_All.pipe_right uu____13337
                               FStar_Syntax_Syntax.mk_binder in
                           [uu____13330] in
                         FStar_Syntax_Subst.open_term uu____13329 body in
                       match uu____13324 with
                       | (bs, body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13364 ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                             let lbname =
                               let x =
                                 let uu____13373 = FStar_List.hd bs in
                                 FStar_Pervasives_Native.fst uu____13373 in
                               FStar_Util.Inl
                                 (let uu___1682_13389 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1682_13389.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1682_13389.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }) in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13392 ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1687_13395 = lb in
                                let uu____13396 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef in
                                let uu____13399 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1687_13395.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1687_13395.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13396;
                                  FStar_Syntax_Syntax.lbattrs = uu____13399;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1687_13395.FStar_Syntax_Syntax.lbpos)
                                } in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2 ->
                                        fun uu____13434 -> dummy :: env2)
                                     env1) in
                              let stack2 = (Cfg cfg) :: stack1 in
                              let cfg1 =
                                let uu___1694_13459 = cfg in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1694_13459.FStar_TypeChecker_Cfg.reifying)
                                } in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13463 ->
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
               let uu____13484 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13484 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13520 =
                               let uu___1710_13521 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1710_13521.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1710_13521.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13520 in
                           let uu____13522 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13522 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env1 xs in
                               let env2 =
                                 let uu____13548 =
                                   FStar_List.map (fun uu____13570 -> dummy)
                                     xs1 in
                                 let uu____13577 =
                                   let uu____13586 =
                                     FStar_List.map
                                       (fun uu____13602 -> dummy) lbs1 in
                                   FStar_List.append uu____13586 env1 in
                                 FStar_List.append uu____13548 uu____13577 in
                               let def_body1 = norm cfg env2 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13622 =
                                       let uu___1724_13623 = rc in
                                       let uu____13624 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1724_13623.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13624;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1724_13623.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13622
                                 | uu____13633 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___1729_13639 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1729_13639.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1729_13639.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1729_13639.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1729_13639.FStar_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu____13649 =
                        FStar_List.map (fun uu____13665 -> dummy) lbs2 in
                      FStar_List.append uu____13649 env1 in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13673 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13673 with
                     | (lbs3, body3) ->
                         let t2 =
                           let uu___1738_13689 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1738_13689.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1738_13689.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs, body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13723 = closure_as_term cfg env1 t1 in
               rebuild cfg env1 stack1 uu____13723
           | FStar_Syntax_Syntax.Tm_let (lbs, body) ->
               let uu____13744 =
                 FStar_List.fold_right
                   (fun lb ->
                      fun uu____13822 ->
                        match uu____13822 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___1754_13947 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1754_13947.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1754_13947.FStar_Syntax_Syntax.sort)
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
               (match uu____13744 with
                | (rec_env, memos, uu____14138) ->
                    let uu____14193 =
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
                             let uu____14442 =
                               let uu____14449 =
                                 let uu____14450 =
                                   let uu____14482 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14482, false) in
                                 Clos uu____14450 in
                               (FStar_Pervasives_Native.None, uu____14449) in
                             uu____14442 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1 in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head, m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14567 ->
                     let uu____14568 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14568);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1, t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14592 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____14596::uu____14597 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l, r, uu____14602) ->
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
                             | uu____14681 -> norm cfg env1 stack1 head)
                        | [] ->
                            let head1 = norm cfg env1 [] head in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names, args) ->
                                  let names1 =
                                    FStar_All.pipe_right names
                                      (FStar_List.map (norm cfg env1 [])) in
                                  let uu____14729 =
                                    let uu____14750 =
                                      norm_pattern_args cfg env1 args in
                                    (names1, uu____14750) in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14729
                              | uu____14779 -> m in
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14785 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14801 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14815 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14829 =
                        let uu____14831 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____14833 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14831 uu____14833 in
                      failwith uu____14829
                    else
                      (let uu____14838 = inline_closure_env cfg env1 [] t2 in
                       rebuild cfg env1 stack1 uu____14838)
                | uu____14839 -> norm cfg env1 stack1 t2))
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
              let uu____14848 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu____14848 with
              | FStar_Pervasives_Native.None ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14862 ->
                        let uu____14863 = FStar_Syntax_Print.fv_to_string f in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14863);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us, t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14876 ->
                        let uu____14877 =
                          FStar_Syntax_Print.term_to_string t0 in
                        let uu____14879 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14877 uu____14879);
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
                      | (UnivArgs (us', uu____14892))::stack2 ->
                          ((let uu____14901 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm") in
                            if uu____14901
                            then
                              FStar_List.iter
                                (fun x ->
                                   let uu____14909 =
                                     FStar_Syntax_Print.univ_to_string x in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14909) us'
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
                      | uu____14945 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____14948 ->
                          let uu____14951 =
                            let uu____14953 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14953 in
                          failwith uu____14951
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
              let uu____14973 =
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
                    let uu___1865_14991 = cfg in
                    let uu____14992 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____14992;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1865_14991.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1865_14991.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1865_14991.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1865_14991.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1865_14991.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1865_14991.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1865_14991.FStar_TypeChecker_Cfg.reifying)
                    } in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1) in
              match uu____14973 with
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
                     (uu____15033,
                      {
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify);
                        FStar_Syntax_Syntax.pos = uu____15034;
                        FStar_Syntax_Syntax.vars = uu____15035;_},
                      uu____15036, uu____15037))::uu____15038
                     -> ()
                 | uu____15043 ->
                     let uu____15046 =
                       let uu____15048 = stack_to_string stack1 in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15048 in
                     failwith uu____15046);
                (let top0 = top in
                 let top1 = FStar_Syntax_Util.unascribe top in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15057 ->
                      let uu____15058 = FStar_Syntax_Print.tag_of_term top1 in
                      let uu____15060 =
                        FStar_Syntax_Print.term_to_string top1 in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15058
                        uu____15060);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1 in
                  let uu____15064 =
                    let uu____15065 = FStar_Syntax_Subst.compress top2 in
                    uu____15065.FStar_Syntax_Syntax.n in
                  match uu____15064 with
                  | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name in
                      let uu____15087 =
                        let uu____15096 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr in
                        FStar_All.pipe_right uu____15096 FStar_Util.must in
                      (match uu____15087 with
                       | (uu____15111, repr) ->
                           let uu____15121 =
                             let uu____15128 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr in
                             FStar_All.pipe_right uu____15128 FStar_Util.must in
                           (match uu____15121 with
                            | (uu____15165, bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15171 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15182 =
                                         let uu____15183 =
                                           FStar_Syntax_Subst.compress e in
                                         uu____15183.FStar_Syntax_Syntax.n in
                                       match uu____15182 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,
                                            FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15189, uu____15190))
                                           ->
                                           let uu____15199 =
                                             let uu____15200 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu____15200.FStar_Syntax_Syntax.n in
                                           (match uu____15199 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,
                                                 FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15206, msrc,
                                                  uu____15208))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15217 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu____15217
                                            | uu____15218 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15219 ->
                                           FStar_Pervasives_Native.None in
                                     let uu____15220 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu____15220 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1944_15225 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1944_15225.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1944_15225.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1944_15225.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1944_15225.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1944_15225.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let uu____15226 =
                                            FStar_List.tl stack1 in
                                          let uu____15227 =
                                            let uu____15228 =
                                              let uu____15229 =
                                                let uu____15243 =
                                                  FStar_Syntax_Util.mk_reify
                                                    body in
                                                ((false, [lb1]), uu____15243) in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu____15229 in
                                            FStar_Syntax_Syntax.mk
                                              uu____15228
                                              top2.FStar_Syntax_Syntax.pos in
                                          norm cfg env1 uu____15226
                                            uu____15227
                                      | FStar_Pervasives_Native.None ->
                                          let uu____15259 =
                                            let uu____15261 = is_return body in
                                            match uu____15261 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15266;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15267;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15270 -> false in
                                          if uu____15259
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
                                               let uu____15298 =
                                                 let uu____15299 =
                                                   let uu____15318 =
                                                     let uu____15327 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         x in
                                                     [uu____15327] in
                                                   (uu____15318, body1,
                                                     (FStar_Pervasives_Native.Some
                                                        body_rc)) in
                                                 FStar_Syntax_Syntax.Tm_abs
                                                   uu____15299 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15298
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close =
                                               closure_as_term cfg env1 in
                                             let bind_inst =
                                               let uu____15366 =
                                                 let uu____15367 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu____15367.FStar_Syntax_Syntax.n in
                                               match uu____15366 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind,
                                                    uu____15373::uu____15374::[])
                                                   ->
                                                   let uu____15379 =
                                                     let uu____15380 =
                                                       let uu____15387 =
                                                         let uu____15388 =
                                                           let uu____15389 =
                                                             close
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.FStar_TypeChecker_Cfg.tcenv
                                                             uu____15389 in
                                                         let uu____15390 =
                                                           let uu____15393 =
                                                             let uu____15394
                                                               = close t in
                                                             (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.FStar_TypeChecker_Cfg.tcenv
                                                               uu____15394 in
                                                           [uu____15393] in
                                                         uu____15388 ::
                                                           uu____15390 in
                                                       (bind, uu____15387) in
                                                     FStar_Syntax_Syntax.Tm_uinst
                                                       uu____15380 in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____15379 rng
                                               | uu____15397 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let bind_inst_args f_arg =
                                               let uu____15409 =
                                                 FStar_Syntax_Util.is_layered
                                                   ed in
                                               if uu____15409
                                               then
                                                 let unit_args =
                                                   let uu____15417 =
                                                     let uu____15418 =
                                                       let uu____15421 =
                                                         let uu____15422 =
                                                           FStar_All.pipe_right
                                                             ed
                                                             FStar_Syntax_Util.get_bind_vc_combinator in
                                                         FStar_All.pipe_right
                                                           uu____15422
                                                           FStar_Pervasives_Native.snd in
                                                       FStar_All.pipe_right
                                                         uu____15421
                                                         FStar_Syntax_Subst.compress in
                                                     uu____15418.FStar_Syntax_Syntax.n in
                                                   match uu____15417 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (uu____15455::uu____15456::bs,
                                                        uu____15458)
                                                       when
                                                       (FStar_List.length bs)
                                                         >=
                                                         (Prims.of_int (2))
                                                       ->
                                                       let uu____15510 =
                                                         let uu____15519 =
                                                           FStar_All.pipe_right
                                                             bs
                                                             (FStar_List.splitAt
                                                                ((FStar_List.length
                                                                    bs)
                                                                   -
                                                                   (Prims.of_int (2)))) in
                                                         FStar_All.pipe_right
                                                           uu____15519
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____15510
                                                         (FStar_List.map
                                                            (fun uu____15642
                                                               ->
                                                               FStar_Syntax_Syntax.as_arg
                                                                 FStar_Syntax_Syntax.unit_const))
                                                   | uu____15649 ->
                                                       let uu____15650 =
                                                         let uu____15656 =
                                                           let uu____15658 =
                                                             FStar_Ident.string_of_lid
                                                               ed.FStar_Syntax_Syntax.mname in
                                                           let uu____15660 =
                                                             let uu____15662
                                                               =
                                                               let uu____15663
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator in
                                                               FStar_All.pipe_right
                                                                 uu____15663
                                                                 FStar_Pervasives_Native.snd in
                                                             FStar_All.pipe_right
                                                               uu____15662
                                                               FStar_Syntax_Print.term_to_string in
                                                           FStar_Util.format2
                                                             "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                             uu____15658
                                                             uu____15660 in
                                                         (FStar_Errors.Fatal_UnexpectedEffect,
                                                           uu____15656) in
                                                       FStar_Errors.raise_error
                                                         uu____15650 rng in
                                                 let uu____15689 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15690 =
                                                   let uu____15693 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15694 =
                                                     let uu____15697 =
                                                       let uu____15700 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           f_arg in
                                                       let uu____15701 =
                                                         let uu____15704 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2 in
                                                         [uu____15704] in
                                                       uu____15700 ::
                                                         uu____15701 in
                                                     FStar_List.append
                                                       unit_args uu____15697 in
                                                   uu____15693 :: uu____15694 in
                                                 uu____15689 :: uu____15690
                                               else
                                                 (let maybe_range_arg =
                                                    let uu____15710 =
                                                      FStar_Util.for_some
                                                        (FStar_Syntax_Util.attr_eq
                                                           FStar_Syntax_Util.dm4f_bind_range_attr)
                                                        ed.FStar_Syntax_Syntax.eff_attrs in
                                                    if uu____15710
                                                    then
                                                      let uu____15715 =
                                                        let uu____15716 =
                                                          FStar_TypeChecker_Cfg.embed_simple
                                                            FStar_Syntax_Embeddings.e_range
                                                            lb.FStar_Syntax_Syntax.lbpos
                                                            lb.FStar_Syntax_Syntax.lbpos in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____15716 in
                                                      let uu____15717 =
                                                        let uu____15720 =
                                                          let uu____15721 =
                                                            FStar_TypeChecker_Cfg.embed_simple
                                                              FStar_Syntax_Embeddings.e_range
                                                              body2.FStar_Syntax_Syntax.pos
                                                              body2.FStar_Syntax_Syntax.pos in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu____15721 in
                                                        [uu____15720] in
                                                      uu____15715 ::
                                                        uu____15717
                                                    else [] in
                                                  let uu____15724 =
                                                    let uu____15727 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp in
                                                    let uu____15728 =
                                                      let uu____15731 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t in
                                                      [uu____15731] in
                                                    uu____15727 ::
                                                      uu____15728 in
                                                  let uu____15732 =
                                                    let uu____15735 =
                                                      let uu____15738 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun in
                                                      let uu____15739 =
                                                        let uu____15742 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            f_arg in
                                                        let uu____15743 =
                                                          let uu____15746 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu____15747 =
                                                            let uu____15750 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2 in
                                                            [uu____15750] in
                                                          uu____15746 ::
                                                            uu____15747 in
                                                        uu____15742 ::
                                                          uu____15743 in
                                                      uu____15738 ::
                                                        uu____15739 in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____15735 in
                                                  FStar_List.append
                                                    uu____15724 uu____15732) in
                                             let reified =
                                               let is_total_effect =
                                                 FStar_TypeChecker_Env.is_total_effect
                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                   eff_name in
                                               if is_total_effect
                                               then
                                                 let uu____15755 =
                                                   let uu____15756 =
                                                     let uu____15773 =
                                                       bind_inst_args head in
                                                     (bind_inst, uu____15773) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____15756 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____15755 rng
                                               else
                                                 (let uu____15798 =
                                                    let bv =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        x.FStar_Syntax_Syntax.sort in
                                                    let lb1 =
                                                      let uu____15807 =
                                                        let uu____15810 =
                                                          let uu____15821 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              x.FStar_Syntax_Syntax.sort in
                                                          [uu____15821] in
                                                        FStar_Syntax_Util.mk_app
                                                          repr uu____15810 in
                                                      {
                                                        FStar_Syntax_Syntax.lbname
                                                          =
                                                          (FStar_Util.Inl bv);
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = [];
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____15807;
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
                                                    let uu____15851 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        bv in
                                                    (lb1, bv, uu____15851) in
                                                  match uu____15798 with
                                                  | (lb_head, head_bv, head1)
                                                      ->
                                                      let uu____15855 =
                                                        let uu____15856 =
                                                          let uu____15870 =
                                                            let uu____15873 =
                                                              let uu____15880
                                                                =
                                                                let uu____15881
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    head_bv in
                                                                [uu____15881] in
                                                              FStar_Syntax_Subst.close
                                                                uu____15880 in
                                                            let uu____15900 =
                                                              let uu____15901
                                                                =
                                                                let uu____15902
                                                                  =
                                                                  let uu____15919
                                                                    =
                                                                    bind_inst_args
                                                                    head1 in
                                                                  (bind_inst,
                                                                    uu____15919) in
                                                                FStar_Syntax_Syntax.Tm_app
                                                                  uu____15902 in
                                                              FStar_Syntax_Syntax.mk
                                                                uu____15901
                                                                rng in
                                                            FStar_All.pipe_left
                                                              uu____15873
                                                              uu____15900 in
                                                          ((false, [lb_head]),
                                                            uu____15870) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu____15856 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu____15855 rng) in
                                             FStar_TypeChecker_Cfg.log cfg
                                               (fun uu____15961 ->
                                                  let uu____15962 =
                                                    FStar_Syntax_Print.term_to_string
                                                      top0 in
                                                  let uu____15964 =
                                                    FStar_Syntax_Print.term_to_string
                                                      reified in
                                                  FStar_Util.print2
                                                    "Reified (1) <%s> to %s\n"
                                                    uu____15962 uu____15964);
                                             (let uu____15967 =
                                                FStar_List.tl stack1 in
                                              norm cfg env1 uu____15967
                                                reified))))))
                  | FStar_Syntax_Syntax.Tm_app (head, args) ->
                      ((let uu____15995 = FStar_Options.defensive () in
                        if uu____15995
                        then
                          let is_arg_impure uu____16010 =
                            match uu____16010 with
                            | (e, q) ->
                                let uu____16024 =
                                  let uu____16025 =
                                    FStar_Syntax_Subst.compress e in
                                  uu____16025.FStar_Syntax_Syntax.n in
                                (match uu____16024 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,
                                      FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1, m2, t'))
                                     ->
                                     let uu____16041 =
                                       FStar_Syntax_Util.is_pure_effect m1 in
                                     Prims.op_Negation uu____16041
                                 | uu____16043 -> false) in
                          let uu____16045 =
                            let uu____16047 =
                              let uu____16058 =
                                FStar_Syntax_Syntax.as_arg head in
                              uu____16058 :: args in
                            FStar_Util.for_some is_arg_impure uu____16047 in
                          (if uu____16045
                           then
                             let uu____16084 =
                               let uu____16090 =
                                 let uu____16092 =
                                   FStar_Syntax_Print.term_to_string top2 in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16092 in
                               (FStar_Errors.Warning_Defensive, uu____16090) in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16084
                           else ())
                        else ());
                       (let fallback1 uu____16105 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16109 ->
                               let uu____16110 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16110 "");
                          (let uu____16114 = FStar_List.tl stack1 in
                           let uu____16115 = FStar_Syntax_Util.mk_reify top2 in
                           norm cfg env1 uu____16114 uu____16115) in
                        let fallback2 uu____16121 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16125 ->
                               let uu____16126 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16126 "");
                          (let uu____16130 = FStar_List.tl stack1 in
                           let uu____16131 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos in
                           norm cfg env1 uu____16130 uu____16131) in
                        let uu____16136 =
                          let uu____16137 = FStar_Syntax_Util.un_uinst head in
                          uu____16137.FStar_Syntax_Syntax.n in
                        match uu____16136 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid in
                            let uu____16143 =
                              let uu____16145 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid in
                              Prims.op_Negation uu____16145 in
                            if uu____16143
                            then fallback1 ()
                            else
                              (let uu____16150 =
                                 let uu____16152 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isNone uu____16152 in
                               if uu____16150
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16167 =
                                      FStar_Syntax_Util.mk_reify head in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____16167
                                      args t.FStar_Syntax_Syntax.pos in
                                  let uu____16168 = FStar_List.tl stack1 in
                                  norm cfg env1 uu____16168 t1))
                        | uu____16169 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic uu____16171) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, t'))
                      ->
                      let lifted =
                        let uu____16195 = closure_as_term cfg env1 t' in
                        reify_lift cfg e msrc mtgt uu____16195 in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16199 ->
                            let uu____16200 =
                              FStar_Syntax_Print.term_to_string lifted in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16200);
                       (let uu____16203 = FStar_List.tl stack1 in
                        norm cfg env1 uu____16203 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e, branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____16324 ->
                                match uu____16324 with
                                | (pat, wopt, tm) ->
                                    let uu____16372 =
                                      FStar_Syntax_Util.mk_reify tm in
                                    (pat, wopt, uu____16372))) in
                      let tm =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos in
                      let uu____16404 = FStar_List.tl stack1 in
                      norm cfg env1 uu____16404 tm
                  | uu____16405 -> fallback ()))
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
              (fun uu____16419 ->
                 let uu____16420 = FStar_Ident.string_of_lid msrc in
                 let uu____16422 = FStar_Ident.string_of_lid mtgt in
                 let uu____16424 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16420
                   uu____16422 uu____16424);
            (let uu____16427 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16430 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1) in
                  Prims.op_Negation uu____16430) in
             if uu____16427
             then
               let ed =
                 let uu____16435 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____16435 in
               let uu____16436 =
                 let uu____16445 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 FStar_All.pipe_right uu____16445 FStar_Util.must in
               match uu____16436 with
               | (uu____16492, repr) ->
                   let uu____16502 =
                     let uu____16511 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr in
                     FStar_All.pipe_right uu____16511 FStar_Util.must in
                   (match uu____16502 with
                    | (uu____16558, return_repr) ->
                        let return_inst =
                          let uu____16571 =
                            let uu____16572 =
                              FStar_Syntax_Subst.compress return_repr in
                            uu____16572.FStar_Syntax_Syntax.n in
                          match uu____16571 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm, uu____16578::[]) ->
                              let uu____16583 =
                                let uu____16584 =
                                  let uu____16591 =
                                    let uu____16592 =
                                      env1.FStar_TypeChecker_Env.universe_of
                                        env1 t in
                                    [uu____16592] in
                                  (return_tm, uu____16591) in
                                FStar_Syntax_Syntax.Tm_uinst uu____16584 in
                              FStar_Syntax_Syntax.mk uu____16583
                                e.FStar_Syntax_Syntax.pos
                          | uu____16595 ->
                              failwith "NIY : Reification of indexed effects" in
                        let uu____16599 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t in
                          let lb =
                            let uu____16610 =
                              let uu____16613 =
                                let uu____16624 =
                                  FStar_Syntax_Syntax.as_arg t in
                                [uu____16624] in
                              FStar_Syntax_Util.mk_app repr uu____16613 in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____16610;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            } in
                          let uu____16651 = FStar_Syntax_Syntax.bv_to_name bv in
                          (lb, bv, uu____16651) in
                        (match uu____16599 with
                         | (lb_e, e_bv, e1) ->
                             let uu____16663 =
                               let uu____16664 =
                                 let uu____16678 =
                                   let uu____16681 =
                                     let uu____16688 =
                                       let uu____16689 =
                                         FStar_Syntax_Syntax.mk_binder e_bv in
                                       [uu____16689] in
                                     FStar_Syntax_Subst.close uu____16688 in
                                   let uu____16708 =
                                     let uu____16709 =
                                       let uu____16710 =
                                         let uu____16727 =
                                           let uu____16738 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____16747 =
                                             let uu____16758 =
                                               FStar_Syntax_Syntax.as_arg e1 in
                                             [uu____16758] in
                                           uu____16738 :: uu____16747 in
                                         (return_inst, uu____16727) in
                                       FStar_Syntax_Syntax.Tm_app uu____16710 in
                                     FStar_Syntax_Syntax.mk uu____16709
                                       e1.FStar_Syntax_Syntax.pos in
                                   FStar_All.pipe_left uu____16681
                                     uu____16708 in
                                 ((false, [lb_e]), uu____16678) in
                               FStar_Syntax_Syntax.Tm_let uu____16664 in
                             FStar_Syntax_Syntax.mk uu____16663
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____16820 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt in
                match uu____16820 with
                | FStar_Pervasives_Native.None ->
                    let uu____16823 =
                      let uu____16825 = FStar_Ident.string_of_lid msrc in
                      let uu____16827 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16825 uu____16827 in
                    failwith uu____16823
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16830;
                      FStar_TypeChecker_Env.mtarget = uu____16831;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16832;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None;_};_}
                    ->
                    let uu____16852 =
                      let uu____16854 = FStar_Ident.string_of_lid msrc in
                      let uu____16856 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16854 uu____16856 in
                    failwith uu____16852
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16859;
                      FStar_TypeChecker_Env.mtarget = uu____16860;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16861;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____16892 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc in
                      if uu____16892
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____16897 =
                           let uu____16898 =
                             let uu____16917 =
                               let uu____16926 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_Syntax_Syntax.t_unit in
                               [uu____16926] in
                             (uu____16917, e,
                               (FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      msrc;
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t);
                                    FStar_Syntax_Syntax.residual_flags = []
                                  })) in
                           FStar_Syntax_Syntax.Tm_abs uu____16898 in
                         FStar_Syntax_Syntax.mk uu____16897
                           e.FStar_Syntax_Syntax.pos) in
                    let uu____16959 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t in
                    lift uu____16959 t e1))
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
                (fun uu____17029 ->
                   match uu____17029 with
                   | (a, imp) ->
                       let uu____17048 = norm cfg env1 [] a in
                       (uu____17048, imp))))
and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg ->
    fun env1 ->
      fun comp ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17058 ->
             let uu____17059 = FStar_Syntax_Print.comp_to_string comp in
             let uu____17061 =
               FStar_Util.string_of_int (FStar_List.length env1) in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17059 uu____17061);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17087 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____17090 ->
                        FStar_Pervasives_Native.Some uu____17090) uu____17087
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2128_17091 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2128_17091.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2128_17091.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17113 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu____17116 ->
                        FStar_Pervasives_Native.Some uu____17116) uu____17113
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___2139_17117 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2139_17117.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2139_17117.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx ->
                    fun uu____17162 ->
                      match uu____17162 with
                      | (a, i) ->
                          let uu____17182 = norm cfg env1 [] a in
                          (uu____17182, i)) in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17204 ->
                       match uu___14_17204 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17208 = norm cfg env1 [] t in
                           FStar_Syntax_Syntax.DECREASES uu____17208
                       | f -> f)) in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ in
             let uu___2156_17216 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2158_17219 = ct in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2158_17219.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2156_17216.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2156_17216.FStar_Syntax_Syntax.vars)
             })
and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg ->
    fun env1 ->
      fun b ->
        let uu____17223 = b in
        match uu____17223 with
        | (x, imp) ->
            let x1 =
              let uu___2166_17231 = x in
              let uu____17232 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2166_17231.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2166_17231.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17232
              } in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
                  let uu____17243 =
                    let uu____17244 =
                      let uu____17245 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____17245 in
                    FStar_Syntax_Syntax.Meta uu____17244 in
                  FStar_Pervasives_Native.Some uu____17243
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
                  let uu____17251 =
                    let uu____17252 =
                      let uu____17253 = closure_as_term cfg env1 t in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____17253 in
                    FStar_Syntax_Syntax.Meta uu____17252 in
                  FStar_Pervasives_Native.Some uu____17251
              | i -> i in
            (x1, imp1)
and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu____17264 =
          FStar_List.fold_left
            (fun uu____17298 ->
               fun b ->
                 match uu____17298 with
                 | (nbs', env2) ->
                     let b1 = norm_binder cfg env2 b in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs in
        match uu____17264 with | (nbs, uu____17378) -> FStar_List.rev nbs
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
            let uu____17410 =
              let uu___2196_17411 = rc in
              let uu____17412 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2196_17411.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17412;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2196_17411.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____17410
        | uu____17430 -> lopt
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
            (let uu____17440 = FStar_Syntax_Print.term_to_string tm in
             let uu____17442 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17440 uu____17442)
          else ();
          tm'
and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg ->
    fun uu___15_17454 ->
      match uu___15_17454 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17467 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l in
          (match uu____17467 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None ->
               let uu____17471 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None in
               FStar_Syntax_Syntax.fv_to_tm uu____17471)
and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let tm1 =
            let uu____17479 = norm_cb cfg in
            reduce_primops uu____17479 cfg env1 tm in
          let uu____17484 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify in
          if uu____17484
          then tm1
          else
            (let w t =
               let uu___2225_17503 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2225_17503.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2225_17503.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               let uu____17515 =
                 let uu____17516 = FStar_Syntax_Util.unmeta t in
                 uu____17516.FStar_Syntax_Syntax.n in
               match uu____17515 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17528 -> FStar_Pervasives_Native.None in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t, uu____17592)::args1, (bv, uu____17595)::bs1) ->
                   let uu____17649 =
                     let uu____17650 = FStar_Syntax_Subst.compress t in
                     uu____17650.FStar_Syntax_Syntax.n in
                   (match uu____17649 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17655 -> false)
               | ([], []) -> true
               | (uu____17686, uu____17687) -> false in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17738 = FStar_Syntax_Print.term_to_string t in
                  let uu____17740 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17738
                    uu____17740)
               else ();
               (let uu____17745 = FStar_Syntax_Util.head_and_args' t in
                match uu____17745 with
                | (hd, args) ->
                    let uu____17784 =
                      let uu____17785 = FStar_Syntax_Subst.compress hd in
                      uu____17785.FStar_Syntax_Syntax.n in
                    (match uu____17784 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____17793 =
                               FStar_Syntax_Print.term_to_string t in
                             let uu____17795 =
                               FStar_Syntax_Print.bv_to_string bv in
                             let uu____17797 =
                               FStar_Syntax_Print.term_to_string hd in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17793 uu____17795 uu____17797)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17802 -> FStar_Pervasives_Native.None)) in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17820 = FStar_Syntax_Print.term_to_string t in
                  let uu____17822 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17820
                    uu____17822)
               else ();
               (let uu____17827 = FStar_Syntax_Util.is_squash t in
                match uu____17827 with
                | FStar_Pervasives_Native.Some (uu____17838, t') ->
                    is_applied bs t'
                | uu____17850 ->
                    let uu____17859 = FStar_Syntax_Util.is_auto_squash t in
                    (match uu____17859 with
                     | FStar_Pervasives_Native.Some (uu____17870, t') ->
                         is_applied bs t'
                     | uu____17882 -> is_applied bs t)) in
             let is_quantified_const bv phi =
               let uu____17906 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____17906 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid, (p, uu____17913)::(q, uu____17915)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17958 = FStar_Syntax_Print.term_to_string p in
                       let uu____17960 = FStar_Syntax_Print.term_to_string q in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17958 uu____17960)
                    else ();
                    (let uu____17965 =
                       FStar_Syntax_Util.destruct_typ_as_formula p in
                     match uu____17965 with
                     | FStar_Pervasives_Native.None ->
                         let uu____17970 =
                           let uu____17971 = FStar_Syntax_Subst.compress p in
                           uu____17971.FStar_Syntax_Syntax.n in
                         (match uu____17970 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17982 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q in
                                FStar_Pervasives_Native.Some uu____17982))
                          | uu____17985 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1, (p1, uu____17988)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18013 =
                           let uu____18014 = FStar_Syntax_Subst.compress p1 in
                           uu____18014.FStar_Syntax_Syntax.n in
                         (match uu____18013 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18025 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q in
                                FStar_Pervasives_Native.Some uu____18025))
                          | uu____18028 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs, pats, phi1)) ->
                         let uu____18032 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1 in
                         (match uu____18032 with
                          | FStar_Pervasives_Native.None ->
                              let uu____18037 =
                                is_applied_maybe_squashed bs phi1 in
                              (match uu____18037 with
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
                                     let uu____18051 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____18051))
                               | uu____18054 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1, (p1, uu____18059)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18084 =
                                is_applied_maybe_squashed bs p1 in
                              (match uu____18084 with
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
                                     let uu____18098 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q in
                                     FStar_Pervasives_Native.Some uu____18098))
                               | uu____18101 -> FStar_Pervasives_Native.None)
                          | uu____18104 -> FStar_Pervasives_Native.None)
                     | uu____18107 -> FStar_Pervasives_Native.None))
               | uu____18110 -> FStar_Pervasives_Native.None in
             let is_forall_const phi =
               let uu____18123 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu____18123 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv, uu____18129)::[], uu____18130, phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18150 = FStar_Syntax_Print.bv_to_string bv in
                       let uu____18152 =
                         FStar_Syntax_Print.term_to_string phi' in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18150
                         uu____18152)
                    else ();
                    is_quantified_const bv phi')
               | uu____18157 -> FStar_Pervasives_Native.None in
             let is_const_match phi =
               let uu____18172 =
                 let uu____18173 = FStar_Syntax_Subst.compress phi in
                 uu____18173.FStar_Syntax_Syntax.n in
               match uu____18172 with
               | FStar_Syntax_Syntax.Tm_match (uu____18179, br::brs) ->
                   let uu____18246 = br in
                   (match uu____18246 with
                    | (uu____18264, uu____18265, e) ->
                        let r =
                          let uu____18287 = simp_t e in
                          match uu____18287 with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18299 =
                                FStar_List.for_all
                                  (fun uu____18318 ->
                                     match uu____18318 with
                                     | (uu____18332, uu____18333, e') ->
                                         let uu____18347 = simp_t e' in
                                         uu____18347 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs in
                              if uu____18299
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None in
                        r)
               | uu____18363 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____18373 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____18373
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18409 =
                 match uu____18409 with
                 | (t1, q) ->
                     let uu____18430 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____18430 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
                      | uu____18462 -> (t1, q)) in
               let uu____18475 = FStar_Syntax_Util.head_and_args t in
               match uu____18475 with
               | (head, args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     t.FStar_Syntax_Syntax.pos in
             let rec clearly_inhabited ty =
               let uu____18553 =
                 let uu____18554 = FStar_Syntax_Util.unmeta ty in
                 uu____18554.FStar_Syntax_Syntax.n in
               match uu____18553 with
               | FStar_Syntax_Syntax.Tm_uinst (t, uu____18559) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18564, c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18588 -> false in
             let simplify arg =
               let uu____18621 = simp_t (FStar_Pervasives_Native.fst arg) in
               (uu____18621, arg) in
             let uu____18636 = is_forall_const tm1 in
             match uu____18636 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18642 = FStar_Syntax_Print.term_to_string tm1 in
                     let uu____18644 = FStar_Syntax_Print.term_to_string tm' in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18642
                       uu____18644)
                  else ();
                  (let uu____18649 = norm cfg env1 [] tm' in
                   maybe_simplify_aux cfg env1 stack1 uu____18649))
             | FStar_Pervasives_Native.None ->
                 let uu____18650 =
                   let uu____18651 = FStar_Syntax_Subst.compress tm1 in
                   uu____18651.FStar_Syntax_Syntax.n in
                 (match uu____18650 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18655;
                              FStar_Syntax_Syntax.vars = uu____18656;_},
                            uu____18657);
                         FStar_Syntax_Syntax.pos = uu____18658;
                         FStar_Syntax_Syntax.vars = uu____18659;_},
                       args)
                      ->
                      let uu____18689 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____18689
                      then
                        let uu____18692 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____18692 with
                         | (FStar_Pervasives_Native.Some (true), uu____18750)::
                             (uu____18751, (arg, uu____18753))::[] ->
                             maybe_auto_squash arg
                         | (uu____18826, (arg, uu____18828))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____18829)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____18902)::uu____18903::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18973::(FStar_Pervasives_Native.Some
                                         (false), uu____18974)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19044 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19062 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____19062
                         then
                           let uu____19065 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____19065 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____19123)::uu____19124::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19194::(FStar_Pervasives_Native.Some
                                           (true), uu____19195)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____19265)::(uu____19266, (arg, uu____19268))::[]
                               -> maybe_auto_squash arg
                           | (uu____19341, (arg, uu____19343))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____19344)::[]
                               -> maybe_auto_squash arg
                           | uu____19417 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19435 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____19435
                            then
                              let uu____19438 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____19438 with
                              | uu____19496::(FStar_Pervasives_Native.Some
                                              (true), uu____19497)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____19567)::uu____19568::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____19638)::(uu____19639,
                                                (arg, uu____19641))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19714, (p, uu____19716))::(uu____19717,
                                                                  (q,
                                                                   uu____19719))::[]
                                  ->
                                  let uu____19791 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____19791
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19796 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19814 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____19814
                               then
                                 let uu____19817 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____19817 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____19875)::(FStar_Pervasives_Native.Some
                                                   (true), uu____19876)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____19950)::(FStar_Pervasives_Native.Some
                                                   (false), uu____19951)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20025)::(FStar_Pervasives_Native.Some
                                                   (false), uu____20026)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20100)::(FStar_Pervasives_Native.Some
                                                   (true), uu____20101)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20175, (arg, uu____20177))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____20178)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____20251)::(uu____20252,
                                                   (arg, uu____20254))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20327, (arg, uu____20329))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____20330)::[]
                                     ->
                                     let uu____20403 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____20403
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____20404)::(uu____20405,
                                                   (arg, uu____20407))::[]
                                     ->
                                     let uu____20480 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____20480
                                 | (uu____20481, (p, uu____20483))::(uu____20484,
                                                                    (q,
                                                                    uu____20486))::[]
                                     ->
                                     let uu____20558 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____20558
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20563 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20581 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____20581
                                  then
                                    let uu____20584 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____20584 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____20642)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____20686)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20730 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20748 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____20748
                                     then
                                       match args with
                                       | (t, uu____20752)::[] ->
                                           let uu____20777 =
                                             let uu____20778 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____20778.FStar_Syntax_Syntax.n in
                                           (match uu____20777 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20781::[], body,
                                                 uu____20783)
                                                ->
                                                let uu____20818 = simp_t body in
                                                (match uu____20818 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20824 -> tm1)
                                            | uu____20828 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20830))::(t, uu____20832)::[]
                                           ->
                                           let uu____20872 =
                                             let uu____20873 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____20873.FStar_Syntax_Syntax.n in
                                           (match uu____20872 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20876::[], body,
                                                 uu____20878)
                                                ->
                                                let uu____20913 = simp_t body in
                                                (match uu____20913 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20921 -> tm1)
                                            | uu____20925 -> tm1)
                                       | uu____20926 -> tm1
                                     else
                                       (let uu____20939 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____20939
                                        then
                                          match args with
                                          | (t, uu____20943)::[] ->
                                              let uu____20968 =
                                                let uu____20969 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____20969.FStar_Syntax_Syntax.n in
                                              (match uu____20968 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20972::[], body,
                                                    uu____20974)
                                                   ->
                                                   let uu____21009 =
                                                     simp_t body in
                                                   (match uu____21009 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21015 -> tm1)
                                               | uu____21019 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21021))::(t, uu____21023)::[]
                                              ->
                                              let uu____21063 =
                                                let uu____21064 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____21064.FStar_Syntax_Syntax.n in
                                              (match uu____21063 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21067::[], body,
                                                    uu____21069)
                                                   ->
                                                   let uu____21104 =
                                                     simp_t body in
                                                   (match uu____21104 with
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
                                                    | uu____21112 -> tm1)
                                               | uu____21116 -> tm1)
                                          | uu____21117 -> tm1
                                        else
                                          (let uu____21130 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____21130
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21133;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21134;_},
                                                uu____21135)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21161;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21162;_},
                                                uu____21163)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21189 -> tm1
                                           else
                                             (let uu____21202 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____21202
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____21216 =
                                                    let uu____21217 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____21217.FStar_Syntax_Syntax.n in
                                                  match uu____21216 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21228 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21242 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____21242
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____21281 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____21281
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21287 =
                                                         let uu____21288 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____21288.FStar_Syntax_Syntax.n in
                                                       match uu____21287 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21291 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____21299 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____21299
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21308
                                                                  =
                                                                  let uu____21309
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____21309.FStar_Syntax_Syntax.n in
                                                                match uu____21308
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____21315)
                                                                    -> hd
                                                                | uu____21340
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____21344
                                                                =
                                                                let uu____21355
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____21355] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21344)
                                                       | uu____21388 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21393 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____21393 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21413 ->
                                                     let uu____21422 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____21422 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21428;
                         FStar_Syntax_Syntax.vars = uu____21429;_},
                       args)
                      ->
                      let uu____21455 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu____21455
                      then
                        let uu____21458 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu____21458 with
                         | (FStar_Pervasives_Native.Some (true), uu____21516)::
                             (uu____21517, (arg, uu____21519))::[] ->
                             maybe_auto_squash arg
                         | (uu____21592, (arg, uu____21594))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu____21595)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false),
                            uu____21668)::uu____21669::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21739::(FStar_Pervasives_Native.Some
                                         (false), uu____21740)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21810 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21828 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu____21828
                         then
                           let uu____21831 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu____21831 with
                           | (FStar_Pervasives_Native.Some (true),
                              uu____21889)::uu____21890::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21960::(FStar_Pervasives_Native.Some
                                           (true), uu____21961)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false),
                              uu____22031)::(uu____22032, (arg, uu____22034))::[]
                               -> maybe_auto_squash arg
                           | (uu____22107, (arg, uu____22109))::(FStar_Pervasives_Native.Some
                                                                 (false),
                                                                 uu____22110)::[]
                               -> maybe_auto_squash arg
                           | uu____22183 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22201 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu____22201
                            then
                              let uu____22204 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu____22204 with
                              | uu____22262::(FStar_Pervasives_Native.Some
                                              (true), uu____22263)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu____22333)::uu____22334::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu____22404)::(uu____22405,
                                                (arg, uu____22407))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22480, (p, uu____22482))::(uu____22483,
                                                                  (q,
                                                                   uu____22485))::[]
                                  ->
                                  let uu____22557 =
                                    FStar_Syntax_Util.term_eq p q in
                                  (if uu____22557
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22562 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22580 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu____22580
                               then
                                 let uu____22583 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu____22583 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____22641)::(FStar_Pervasives_Native.Some
                                                   (true), uu____22642)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____22716)::(FStar_Pervasives_Native.Some
                                                   (false), uu____22717)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____22791)::(FStar_Pervasives_Native.Some
                                                   (false), uu____22792)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____22866)::(FStar_Pervasives_Native.Some
                                                   (true), uu____22867)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22941, (arg, uu____22943))::
                                     (FStar_Pervasives_Native.Some (true),
                                      uu____22944)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu____23017)::(uu____23018,
                                                   (arg, uu____23020))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23093, (arg, uu____23095))::
                                     (FStar_Pervasives_Native.Some (false),
                                      uu____23096)::[]
                                     ->
                                     let uu____23169 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____23169
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu____23170)::(uu____23171,
                                                   (arg, uu____23173))::[]
                                     ->
                                     let uu____23246 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu____23246
                                 | (uu____23247, (p, uu____23249))::(uu____23250,
                                                                    (q,
                                                                    uu____23252))::[]
                                     ->
                                     let uu____23324 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu____23324
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23329 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23347 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu____23347
                                  then
                                    let uu____23350 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu____23350 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu____23408)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu____23452)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23496 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23514 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu____23514
                                     then
                                       match args with
                                       | (t, uu____23518)::[] ->
                                           let uu____23543 =
                                             let uu____23544 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____23544.FStar_Syntax_Syntax.n in
                                           (match uu____23543 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23547::[], body,
                                                 uu____23549)
                                                ->
                                                let uu____23584 = simp_t body in
                                                (match uu____23584 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23590 -> tm1)
                                            | uu____23594 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23596))::(t, uu____23598)::[]
                                           ->
                                           let uu____23638 =
                                             let uu____23639 =
                                               FStar_Syntax_Subst.compress t in
                                             uu____23639.FStar_Syntax_Syntax.n in
                                           (match uu____23638 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23642::[], body,
                                                 uu____23644)
                                                ->
                                                let uu____23679 = simp_t body in
                                                (match uu____23679 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23687 -> tm1)
                                            | uu____23691 -> tm1)
                                       | uu____23692 -> tm1
                                     else
                                       (let uu____23705 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu____23705
                                        then
                                          match args with
                                          | (t, uu____23709)::[] ->
                                              let uu____23734 =
                                                let uu____23735 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____23735.FStar_Syntax_Syntax.n in
                                              (match uu____23734 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23738::[], body,
                                                    uu____23740)
                                                   ->
                                                   let uu____23775 =
                                                     simp_t body in
                                                   (match uu____23775 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23781 -> tm1)
                                               | uu____23785 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23787))::(t, uu____23789)::[]
                                              ->
                                              let uu____23829 =
                                                let uu____23830 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____23830.FStar_Syntax_Syntax.n in
                                              (match uu____23829 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23833::[], body,
                                                    uu____23835)
                                                   ->
                                                   let uu____23870 =
                                                     simp_t body in
                                                   (match uu____23870 with
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
                                                    | uu____23878 -> tm1)
                                               | uu____23882 -> tm1)
                                          | uu____23883 -> tm1
                                        else
                                          (let uu____23896 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu____23896
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23899;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23900;_},
                                                uu____23901)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23927;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23928;_},
                                                uu____23929)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23955 -> tm1
                                           else
                                             (let uu____23968 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu____23968
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu____23982 =
                                                    let uu____23983 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu____23983.FStar_Syntax_Syntax.n in
                                                  match uu____23982 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____23994 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24008 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu____24008
                                                       FStar_Pervasives_Native.fst in
                                                   let uu____24043 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu____24043
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24049 =
                                                         let uu____24050 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu____24050.FStar_Syntax_Syntax.n in
                                                       match uu____24049 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24053 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu____24061 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu____24061
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24070
                                                                  =
                                                                  let uu____24071
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu____24071.FStar_Syntax_Syntax.n in
                                                                match uu____24070
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu____24077)
                                                                    -> hd
                                                                | uu____24102
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu____24106
                                                                =
                                                                let uu____24117
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____24117] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24106)
                                                       | uu____24150 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24155 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu____24155 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24175 ->
                                                     let uu____24184 =
                                                       norm_cb cfg in
                                                     reduce_equality
                                                       uu____24184 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
                      let uu____24195 = simp_t t in
                      (match uu____24195 with
                       | FStar_Pervasives_Native.Some (true) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false) -> tm1
                       | FStar_Pervasives_Native.None -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24204 ->
                      let uu____24227 = is_const_match tm1 in
                      (match uu____24227 with
                       | FStar_Pervasives_Native.Some (true) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None -> tm1)
                  | uu____24236 -> tm1))
and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24246 ->
               (let uu____24248 = FStar_Syntax_Print.tag_of_term t in
                let uu____24250 = FStar_Syntax_Print.term_to_string t in
                let uu____24252 =
                  FStar_Util.string_of_int (FStar_List.length env1) in
                let uu____24260 =
                  let uu____24262 =
                    let uu____24265 = firstn (Prims.of_int (4)) stack1 in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24265 in
                  stack_to_string uu____24262 in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24248 uu____24250 uu____24252 uu____24260);
               (let uu____24290 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild") in
                if uu____24290
                then
                  let uu____24294 = FStar_Syntax_Util.unbound_variables t in
                  match uu____24294 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24301 = FStar_Syntax_Print.tag_of_term t in
                        let uu____24303 = FStar_Syntax_Print.term_to_string t in
                        let uu____24305 =
                          let uu____24307 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string) in
                          FStar_All.pipe_right uu____24307
                            (FStar_String.concat ", ") in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24301
                          uu____24303 uu____24305);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t in
           let uu____24329 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____24337)::uu____24338 -> true
                | uu____24348 -> false) in
           if uu____24329
           then
             let uu____24351 = FStar_All.pipe_right f_opt FStar_Util.must in
             FStar_All.pipe_right uu____24351 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t in
              match stack1 with
              | [] -> t1
              | (Debug (tm, time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now () in
                      let uu____24365 =
                        let uu____24367 =
                          let uu____24369 =
                            FStar_Util.time_diff time_then time_now in
                          FStar_Pervasives_Native.snd uu____24369 in
                        FStar_Util.string_of_int uu____24367 in
                      let uu____24376 = FStar_Syntax_Print.term_to_string tm in
                      let uu____24378 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg in
                      let uu____24380 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24365 uu____24376 uu____24378 uu____24380)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____24389, m, r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24418 ->
                        let uu____24419 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24419);
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
                  let uu____24462 =
                    let uu___2854_24463 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2854_24463.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2854_24463.FStar_Syntax_Syntax.vars)
                    } in
                  rebuild cfg env1 stack2 uu____24462
              | (Arg
                  (Univ uu____24466, uu____24467, uu____24468))::uu____24469
                  -> failwith "Impossible"
              | (Arg (Dummy, uu____24473, uu____24474))::uu____24475 ->
                  failwith "Impossible"
              | (UnivArgs (us, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg, tm, uu____24491, uu____24492), aq, r))::stack2
                  when
                  let uu____24544 = head_of t1 in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24544 ->
                  let t2 =
                    let uu____24546 =
                      let uu____24547 = closure_as_term cfg env_arg tm in
                      (uu____24547, aq) in
                    FStar_Syntax_Syntax.extend_app t1 uu____24546 r in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg, tm, m, uu____24557), aq, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24612 ->
                        let uu____24613 =
                          FStar_Syntax_Print.term_to_string tm in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24613);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (let uu____24617 =
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          &&
                          (let uu____24620 = is_partial_primop_app cfg t1 in
                           Prims.op_Negation uu____24620) in
                      if uu____24617
                      then
                        let arg = closure_as_term cfg env_arg tm in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2 in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu____24636 = FStar_ST.op_Bang m in
                      match uu____24636 with
                      | FStar_Pervasives_Native.None ->
                          let uu____24710 =
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                              &&
                              (let uu____24713 = is_partial_primop_app cfg t1 in
                               Prims.op_Negation uu____24713) in
                          if uu____24710
                          then
                            let arg = closure_as_term cfg env_arg tm in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                            rebuild cfg env_arg stack2 t2
                          else
                            (let stack3 = (MemoLazy m) ::
                               (App (env1, t1, aq, r)) :: stack2 in
                             norm cfg env_arg stack3 tm)
                      | FStar_Pervasives_Native.Some (uu____24727, a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq) r in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2, head, aq, r))::stack' when
                  should_reify cfg stack1 ->
                  let t0 = t1 in
                  let fallback msg uu____24781 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____24786 ->
                         let uu____24787 =
                           FStar_Syntax_Print.term_to_string t1 in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____24787);
                    (let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                     rebuild cfg env2 stack' t2) in
                  let uu____24795 =
                    let uu____24796 = FStar_Syntax_Subst.compress t1 in
                    uu____24796.FStar_Syntax_Syntax.n in
                  (match uu____24795 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, ty))
                       ->
                       let lifted =
                         let uu____24824 = closure_as_term cfg env2 ty in
                         reify_lift cfg t2 msrc mtgt uu____24824 in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____24828 ->
                             let uu____24829 =
                               FStar_Syntax_Print.term_to_string lifted in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____24829);
                        (let uu____24832 = FStar_List.tl stack1 in
                         norm cfg env2 uu____24832 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____24833);
                          FStar_Syntax_Syntax.pos = uu____24834;
                          FStar_Syntax_Syntax.vars = uu____24835;_},
                        (e, uu____24837)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____24876 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____24893 = FStar_Syntax_Util.head_and_args t1 in
                       (match uu____24893 with
                        | (hd, args) ->
                            let uu____24936 =
                              let uu____24937 = FStar_Syntax_Util.un_uinst hd in
                              uu____24937.FStar_Syntax_Syntax.n in
                            (match uu____24936 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____24941 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv in
                                 (match uu____24941 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____24944;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____24945;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____24946;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____24948;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____24949;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____24950;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____24951;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____24987 -> fallback " (3)" ())
                             | uu____24991 -> fallback " (4)" ()))
                   | uu____24993 -> fallback " (2)" ())
              | (App (env2, head, aq, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env', head, aq, r))::stack2 ->
                  let uu____25014 =
                    let uu____25015 =
                      let uu____25016 =
                        let uu____25023 =
                          let uu____25024 =
                            let uu____25056 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            (env1, t1, uu____25056, false) in
                          Clos uu____25024 in
                        (uu____25023, aq, (t1.FStar_Syntax_Syntax.pos)) in
                      Arg uu____25016 in
                    uu____25015 :: stack2 in
                  norm cfg env' uu____25014 head
              | (Match (env', branches1, cfg1, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25131 ->
                        let uu____25132 =
                          FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25132);
                   (let scrutinee_env = env1 in
                    let env2 = env' in
                    let scrutinee = t1 in
                    let norm_and_rebuild_match uu____25143 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25148 ->
                           let uu____25149 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           let uu____25151 =
                             let uu____25153 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____25183 ->
                                       match uu____25183 with
                                       | (p, uu____25194, uu____25195) ->
                                           FStar_Syntax_Print.pat_to_string p)) in
                             FStar_All.pipe_right uu____25153
                               (FStar_String.concat "\n\t") in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25149 uu____25151);
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
                                   (fun uu___16_25220 ->
                                      match uu___16_25220 with
                                      | FStar_TypeChecker_Env.InliningDelta
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                          -> true
                                      | uu____25224 -> false)) in
                            let steps =
                              let uu___3031_25227 =
                                cfg1.FStar_TypeChecker_Cfg.steps in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3031_25227.FStar_TypeChecker_Cfg.for_extraction)
                              } in
                            let uu___3034_25234 = cfg1 in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3034_25234.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3034_25234.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3034_25234.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3034_25234.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3034_25234.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3034_25234.FStar_TypeChecker_Cfg.reifying)
                            }) in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2 in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25309 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                             let uu____25340 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25429 ->
                                       fun uu____25430 ->
                                         match (uu____25429, uu____25430)
                                         with
                                         | ((pats1, env4), (p1, b)) ->
                                             let uu____25580 =
                                               norm_pat env4 p1 in
                                             (match uu____25580 with
                                              | (p2, env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3)) in
                             (match uu____25340 with
                              | (pats1, env4) ->
                                  ((let uu___3062_25750 = p in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3062_25750.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3066_25771 = x in
                               let uu____25772 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3066_25771.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3066_25771.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25772
                               } in
                             ((let uu___3069_25786 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3069_25786.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3073_25797 = x in
                               let uu____25798 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3073_25797.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3073_25797.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25798
                               } in
                             ((let uu___3076_25812 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3076_25812.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                             let x1 =
                               let uu___3082_25828 = x in
                               let uu____25829 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3082_25828.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3082_25828.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25829
                               } in
                             let t3 = norm_or_whnf env3 t2 in
                             ((let uu___3086_25844 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3086_25844.FStar_Syntax_Syntax.p)
                               }), env3) in
                       let branches2 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____25888 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch ->
                                     let uu____25918 =
                                       FStar_Syntax_Subst.open_branch branch in
                                     match uu____25918 with
                                     | (p, wopt, e) ->
                                         let uu____25938 = norm_pat env2 p in
                                         (match uu____25938 with
                                          | (p1, env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____25993 =
                                                      norm_or_whnf env3 w in
                                                    FStar_Pervasives_Native.Some
                                                      uu____25993 in
                                              let e1 = norm_or_whnf env3 e in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1)))) in
                       let scrutinee1 =
                         let uu____26010 =
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
                         if uu____26010
                         then
                           norm
                             (let uu___3105_26017 = cfg1 in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3107_26020 =
                                     cfg1.FStar_TypeChecker_Cfg.steps in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3107_26020.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3105_26017.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee in
                       let uu____26024 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches2)) r in
                       rebuild cfg1 env2 stack2 uu____26024) in
                    let rec is_cons head =
                      let uu____26050 =
                        let uu____26051 = FStar_Syntax_Subst.compress head in
                        uu____26051.FStar_Syntax_Syntax.n in
                      match uu____26050 with
                      | FStar_Syntax_Syntax.Tm_uinst (h, uu____26056) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26061 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26063;
                            FStar_Syntax_Syntax.fv_delta = uu____26064;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor);_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26066;
                            FStar_Syntax_Syntax.fv_delta = uu____26067;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26068);_}
                          -> true
                      | uu____26076 -> false in
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
                      let uu____26245 =
                        FStar_Syntax_Util.head_and_args scrutinee2 in
                      match uu____26245 with
                      | (head, args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26342 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26384 ->
                                    let uu____26385 =
                                      let uu____26387 = is_cons head in
                                      Prims.op_Negation uu____26387 in
                                    FStar_Util.Inr uu____26385)
                           | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                               let uu____26416 =
                                 let uu____26417 =
                                   FStar_Syntax_Util.un_uinst head in
                                 uu____26417.FStar_Syntax_Syntax.n in
                               (match uu____26416 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26436 ->
                                    let uu____26437 =
                                      let uu____26439 = is_cons head in
                                      Prims.op_Negation uu____26439 in
                                    FStar_Util.Inr uu____26437))
                    and matches_args out a p =
                      match (a, p) with
                      | ([], []) -> FStar_Util.Inl out
                      | ((t2, uu____26530)::rest_a,
                         (p1, uu____26533)::rest_p) ->
                          let uu____26592 = matches_pat t2 p1 in
                          (match uu____26592 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26645 -> FStar_Util.Inr false in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1, wopt, b)::rest ->
                          let uu____26768 = matches_pat scrutinee1 p1 in
                          (match uu____26768 with
                           | FStar_Util.Inr (false) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____26814 ->
                                     let uu____26815 =
                                       FStar_Syntax_Print.pat_to_string p1 in
                                     let uu____26817 =
                                       let uu____26819 =
                                         FStar_List.map
                                           (fun uu____26831 ->
                                              match uu____26831 with
                                              | (uu____26837, t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s in
                                       FStar_All.pipe_right uu____26819
                                         (FStar_String.concat "; ") in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____26815 uu____26817);
                                (let env0 = env2 in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3 ->
                                        fun uu____26873 ->
                                          match uu____26873 with
                                          | (bv, t2) ->
                                              let uu____26896 =
                                                let uu____26903 =
                                                  let uu____26906 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv in
                                                  FStar_Pervasives_Native.Some
                                                    uu____26906 in
                                                let uu____26907 =
                                                  let uu____26908 =
                                                    let uu____26940 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2)) in
                                                    ([], t2, uu____26940,
                                                      false) in
                                                  Clos uu____26908 in
                                                (uu____26903, uu____26907) in
                                              uu____26896 :: env3) env2 s in
                                 let uu____27033 =
                                   guard_when_clause wopt b rest in
                                 norm cfg1 env3 stack2 uu____27033))) in
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
            (fun uu____27066 ->
               let uu____27067 = FStar_TypeChecker_Cfg.cfg_to_string c in
               FStar_Util.print1 "Cfg = %s\n" uu____27067);
          (let uu____27070 = is_nbe_request s in
           if uu____27070
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27076 ->
                   let uu____27077 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27077);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27083 ->
                   let uu____27084 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27084);
              (let uu____27087 =
                 FStar_Util.record_time (fun uu____27094 -> nbe_eval c s t) in
               match uu____27087 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27103 ->
                         let uu____27104 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____27106 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27104 uu____27106);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27114 ->
                   let uu____27115 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27115);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27121 ->
                   let uu____27122 = FStar_TypeChecker_Cfg.cfg_to_string c in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27122);
              (let uu____27125 =
                 FStar_Util.record_time (fun uu____27132 -> norm c [] [] t) in
               match uu____27125 with
               | (r, ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27147 ->
                         let uu____27148 =
                           FStar_Syntax_Print.term_to_string r in
                         let uu____27150 = FStar_Util.string_of_int ms in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27148 uu____27150);
                    r))))
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        let uu____27169 =
          let uu____27173 =
            let uu____27175 = FStar_TypeChecker_Env.current_module e in
            FStar_Ident.string_of_lid uu____27175 in
          FStar_Pervasives_Native.Some uu____27173 in
        FStar_Profiling.profile
          (fun uu____27178 -> normalize_with_primitive_steps [] s e t)
          uu____27169 "FStar.TypeChecker.Normalize"
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
          (fun uu____27200 ->
             let uu____27201 = FStar_Syntax_Print.comp_to_string c in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27201);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27207 ->
             let uu____27208 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27208);
        (let uu____27211 =
           FStar_Util.record_time (fun uu____27218 -> norm_comp cfg [] c) in
         match uu____27211 with
         | (c1, ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27233 ->
                   let uu____27234 = FStar_Syntax_Print.comp_to_string c1 in
                   let uu____27236 = FStar_Util.string_of_int ms in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27234
                     uu____27236);
              c1))
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1 ->
    fun u ->
      let uu____27250 = FStar_TypeChecker_Cfg.config [] env1 in
      norm_universe uu____27250 [] u
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
      let uu____27272 = normalize steps env1 t in
      FStar_TypeChecker_Env.non_informative env1 uu____27272
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1 ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27284 -> c
      | FStar_Syntax_Syntax.GTotal (t, uopt) when non_info_norm env1 t ->
          let uu___3275_27303 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3275_27303.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3275_27303.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____27310 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ) in
          if uu____27310
          then
            let ct1 =
              let uu____27314 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name in
              match uu____27314 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27321 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu____27321
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___3285_27328 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3285_27328.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3285_27328.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3285_27328.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c in
                  let uu___3289_27330 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3289_27330.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3289_27330.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3289_27330.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3289_27330.FStar_Syntax_Syntax.flags)
                  } in
            let uu___3292_27331 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3292_27331.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3292_27331.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27334 -> c
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1 ->
    fun lc ->
      let uu____27346 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ) in
      if uu____27346
      then
        let uu____27349 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name in
        match uu____27349 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3300_27353 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g -> g) lc in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3300_27353.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3300_27353.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3300_27353.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None -> lc
      else lc
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1 ->
    fun t ->
      let t1 =
        try
          (fun uu___3307_27372 ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3306_27375 ->
            ((let uu____27377 =
                let uu____27383 =
                  let uu____27385 = FStar_Util.message_of_exn uu___3306_27375 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27385 in
                (FStar_Errors.Warning_NormalizationFailure, uu____27383) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27377);
             t) in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1 ->
    fun c ->
      let c1 =
        try
          (fun uu___3317_27404 ->
             match () with
             | () ->
                 let uu____27405 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1 in
                 norm_comp uu____27405 [] c) ()
        with
        | uu___3316_27414 ->
            ((let uu____27416 =
                let uu____27422 =
                  let uu____27424 = FStar_Util.message_of_exn uu___3316_27414 in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27424 in
                (FStar_Errors.Warning_NormalizationFailure, uu____27422) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27416);
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
                   let uu____27473 =
                     let uu____27474 =
                       let uu____27481 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi in
                       (y, uu____27481) in
                     FStar_Syntax_Syntax.Tm_refine uu____27474 in
                   FStar_Syntax_Syntax.mk uu____27473
                     t01.FStar_Syntax_Syntax.pos
               | uu____27486 -> t2)
          | uu____27487 -> t2 in
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
        let uu____27581 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____27581 with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu____27594 ->
                 let uu____27595 = FStar_Syntax_Util.abs_formals e in
                 (match uu____27595 with
                  | (actuals, uu____27605, uu____27606) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27626 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____27626 with
                         | (binders, args) ->
                             let uu____27637 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____27637
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
      | uu____27652 ->
          let uu____27653 = FStar_Syntax_Util.head_and_args t in
          (match uu____27653 with
           | (head, args) ->
               let uu____27696 =
                 let uu____27697 = FStar_Syntax_Subst.compress head in
                 uu____27697.FStar_Syntax_Syntax.n in
               (match uu____27696 with
                | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
                    let uu____27718 =
                      let uu____27725 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ in
                      FStar_Syntax_Util.arrow_formals uu____27725 in
                    (match uu____27718 with
                     | (formals, _tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27749 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3387_27757 = env1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3387_27757.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3387_27757.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3387_27757.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3387_27757.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3387_27757.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3387_27757.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3387_27757.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3387_27757.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3387_27757.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3387_27757.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3387_27757.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3387_27757.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3387_27757.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3387_27757.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3387_27757.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3387_27757.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3387_27757.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3387_27757.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3387_27757.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3387_27757.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3387_27757.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3387_27757.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3387_27757.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3387_27757.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3387_27757.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3387_27757.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3387_27757.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3387_27757.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3387_27757.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3387_27757.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3387_27757.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3387_27757.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3387_27757.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3387_27757.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3387_27757.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3387_27757.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3387_27757.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3387_27757.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3387_27757.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3387_27757.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3387_27757.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3387_27757.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3387_27757.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___3387_27757.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) t in
                            match uu____27749 with
                            | (uu____27760, ty, uu____27762) ->
                                eta_expand_with_type env1 t ty))
                | uu____27763 ->
                    let uu____27764 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3394_27772 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3394_27772.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3394_27772.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3394_27772.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3394_27772.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3394_27772.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3394_27772.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3394_27772.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3394_27772.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3394_27772.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3394_27772.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3394_27772.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3394_27772.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3394_27772.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3394_27772.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3394_27772.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3394_27772.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3394_27772.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3394_27772.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3394_27772.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3394_27772.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3394_27772.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3394_27772.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3394_27772.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3394_27772.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3394_27772.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3394_27772.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3394_27772.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3394_27772.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3394_27772.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3394_27772.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3394_27772.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3394_27772.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3394_27772.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3394_27772.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3394_27772.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3394_27772.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3394_27772.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3394_27772.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3394_27772.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3394_27772.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3394_27772.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3394_27772.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3394_27772.FStar_TypeChecker_Env.erasable_types_tab);
                           FStar_TypeChecker_Env.enable_defer_to_tac =
                             (uu___3394_27772.FStar_TypeChecker_Env.enable_defer_to_tac)
                         }) t in
                    (match uu____27764 with
                     | (uu____27775, ty, uu____27777) ->
                         eta_expand_with_type env1 t ty)))
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___3406_27859 = x in
      let uu____27860 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3406_27859.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3406_27859.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27860
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27863 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27879 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27880 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27881 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27882 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27889 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27890 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27891 -> t1
    | FStar_Syntax_Syntax.Tm_unknown -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) ->
        let elim_rc rc =
          let uu___3432_27925 = rc in
          let uu____27926 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____27935 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3432_27925.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27926;
            FStar_Syntax_Syntax.residual_flags = uu____27935
          } in
        let uu____27938 =
          let uu____27939 =
            let uu____27958 = elim_delayed_subst_binders bs in
            let uu____27967 = elim_delayed_subst_term t2 in
            let uu____27970 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____27958, uu____27967, uu____27970) in
          FStar_Syntax_Syntax.Tm_abs uu____27939 in
        mk uu____27938
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____28007 =
          let uu____28008 =
            let uu____28023 = elim_delayed_subst_binders bs in
            let uu____28032 = elim_delayed_subst_comp c in
            (uu____28023, uu____28032) in
          FStar_Syntax_Syntax.Tm_arrow uu____28008 in
        mk uu____28007
    | FStar_Syntax_Syntax.Tm_refine (bv, phi) ->
        let uu____28051 =
          let uu____28052 =
            let uu____28059 = elim_bv bv in
            let uu____28060 = elim_delayed_subst_term phi in
            (uu____28059, uu____28060) in
          FStar_Syntax_Syntax.Tm_refine uu____28052 in
        mk uu____28051
    | FStar_Syntax_Syntax.Tm_app (t2, args) ->
        let uu____28091 =
          let uu____28092 =
            let uu____28109 = elim_delayed_subst_term t2 in
            let uu____28112 = elim_delayed_subst_args args in
            (uu____28109, uu____28112) in
          FStar_Syntax_Syntax.Tm_app uu____28092 in
        mk uu____28091
    | FStar_Syntax_Syntax.Tm_match (t2, branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3454_28184 = p in
              let uu____28185 =
                let uu____28186 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____28186 in
              {
                FStar_Syntax_Syntax.v = uu____28185;
                FStar_Syntax_Syntax.p =
                  (uu___3454_28184.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3458_28188 = p in
              let uu____28189 =
                let uu____28190 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____28190 in
              {
                FStar_Syntax_Syntax.v = uu____28189;
                FStar_Syntax_Syntax.p =
                  (uu___3458_28188.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x, t0) ->
              let uu___3464_28197 = p in
              let uu____28198 =
                let uu____28199 =
                  let uu____28206 = elim_bv x in
                  let uu____28207 = elim_delayed_subst_term t0 in
                  (uu____28206, uu____28207) in
                FStar_Syntax_Syntax.Pat_dot_term uu____28199 in
              {
                FStar_Syntax_Syntax.v = uu____28198;
                FStar_Syntax_Syntax.p =
                  (uu___3464_28197.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu___3470_28232 = p in
              let uu____28233 =
                let uu____28234 =
                  let uu____28248 =
                    FStar_List.map
                      (fun uu____28274 ->
                         match uu____28274 with
                         | (x, b) ->
                             let uu____28291 = elim_pat x in (uu____28291, b))
                      pats in
                  (fv, uu____28248) in
                FStar_Syntax_Syntax.Pat_cons uu____28234 in
              {
                FStar_Syntax_Syntax.v = uu____28233;
                FStar_Syntax_Syntax.p =
                  (uu___3470_28232.FStar_Syntax_Syntax.p)
              }
          | uu____28306 -> p in
        let elim_branch uu____28330 =
          match uu____28330 with
          | (pat, wopt, t3) ->
              let uu____28356 = elim_pat pat in
              let uu____28359 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____28362 = elim_delayed_subst_term t3 in
              (uu____28356, uu____28359, uu____28362) in
        let uu____28367 =
          let uu____28368 =
            let uu____28391 = elim_delayed_subst_term t2 in
            let uu____28394 = FStar_List.map elim_branch branches1 in
            (uu____28391, uu____28394) in
          FStar_Syntax_Syntax.Tm_match uu____28368 in
        mk uu____28367
    | FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) ->
        let elim_ascription uu____28525 =
          match uu____28525 with
          | (tc, topt) ->
              let uu____28560 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28570 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____28570
                | FStar_Util.Inr c ->
                    let uu____28572 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____28572 in
              let uu____28573 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____28560, uu____28573) in
        let uu____28582 =
          let uu____28583 =
            let uu____28610 = elim_delayed_subst_term t2 in
            let uu____28613 = elim_ascription a in
            (uu____28610, uu____28613, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____28583 in
        mk uu____28582
    | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
        let elim_lb lb =
          let uu___3500_28676 = lb in
          let uu____28677 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____28680 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3500_28676.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3500_28676.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28677;
            FStar_Syntax_Syntax.lbeff =
              (uu___3500_28676.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28680;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3500_28676.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3500_28676.FStar_Syntax_Syntax.lbpos)
          } in
        let uu____28683 =
          let uu____28684 =
            let uu____28698 =
              let uu____28706 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____28706) in
            let uu____28718 = elim_delayed_subst_term t2 in
            (uu____28698, uu____28718) in
          FStar_Syntax_Syntax.Tm_let uu____28684 in
        mk uu____28683
    | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
        mk (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi in
        let uu____28763 =
          let uu____28764 =
            let uu____28771 = elim_delayed_subst_term tm in
            (uu____28771, qi1) in
          FStar_Syntax_Syntax.Tm_quoted uu____28764 in
        mk uu____28763
    | FStar_Syntax_Syntax.Tm_meta (t2, md) ->
        let uu____28782 =
          let uu____28783 =
            let uu____28790 = elim_delayed_subst_term t2 in
            let uu____28793 = elim_delayed_subst_meta md in
            (uu____28790, uu____28793) in
          FStar_Syntax_Syntax.Tm_meta uu____28783 in
        mk uu____28782
and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_List.map
      (fun uu___17_28802 ->
         match uu___17_28802 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28806 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____28806
         | f -> f) flags
and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c ->
    let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uopt) ->
        let uu____28829 =
          let uu____28830 =
            let uu____28839 = elim_delayed_subst_term t in
            (uu____28839, uopt) in
          FStar_Syntax_Syntax.Total uu____28830 in
        mk uu____28829
    | FStar_Syntax_Syntax.GTotal (t, uopt) ->
        let uu____28856 =
          let uu____28857 =
            let uu____28866 = elim_delayed_subst_term t in
            (uu____28866, uopt) in
          FStar_Syntax_Syntax.GTotal uu____28857 in
        mk uu____28856
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3533_28875 = ct in
          let uu____28876 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____28879 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____28890 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3533_28875.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3533_28875.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28876;
            FStar_Syntax_Syntax.effect_args = uu____28879;
            FStar_Syntax_Syntax.flags = uu____28890
          } in
        mk (FStar_Syntax_Syntax.Comp ct1)
and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_28893 ->
    match uu___18_28893 with
    | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
        let uu____28928 =
          let uu____28949 = FStar_List.map elim_delayed_subst_term names in
          let uu____28958 = FStar_List.map elim_delayed_subst_args args in
          (uu____28949, uu____28958) in
        FStar_Syntax_Syntax.Meta_pattern uu____28928
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____29013 =
          let uu____29020 = elim_delayed_subst_term t in (m, uu____29020) in
        FStar_Syntax_Syntax.Meta_monadic uu____29013
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) ->
        let uu____29032 =
          let uu____29041 = elim_delayed_subst_term t in
          (m1, m2, uu____29041) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29032
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
      (fun uu____29074 ->
         match uu____29074 with
         | (t, q) ->
             let uu____29093 = elim_delayed_subst_term t in (uu____29093, q))
      args
and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs ->
    FStar_List.map
      (fun uu____29121 ->
         match uu____29121 with
         | (x, q) ->
             let uu____29140 =
               let uu___3559_29141 = x in
               let uu____29142 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3559_29141.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3559_29141.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29142
               } in
             (uu____29140, q)) bs
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
            | (uu____29250, FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  c.FStar_Syntax_Syntax.pos
            | (uu____29282, FStar_Util.Inl t) ->
                let uu____29304 =
                  let uu____29305 =
                    let uu____29320 = FStar_Syntax_Syntax.mk_Total t in
                    (binders, uu____29320) in
                  FStar_Syntax_Syntax.Tm_arrow uu____29305 in
                FStar_Syntax_Syntax.mk uu____29304 t.FStar_Syntax_Syntax.pos in
          let uu____29333 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____29333 with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env1 t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____29365 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29438 ->
                    let uu____29439 =
                      let uu____29448 =
                        let uu____29449 = FStar_Syntax_Subst.compress t4 in
                        uu____29449.FStar_Syntax_Syntax.n in
                      (uu____29448, tc) in
                    (match uu____29439 with
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inr uu____29478) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Util.Inl uu____29525) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29570, FStar_Util.Inl uu____29571) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29602 -> failwith "Impossible") in
              (match uu____29365 with
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
          let uu____29741 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t) in
          match uu____29741 with
          | (univ_names1, binders1, tc) ->
              let uu____29815 = FStar_Util.left tc in
              (univ_names1, binders1, uu____29815)
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
          let uu____29869 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c) in
          match uu____29869 with
          | (univ_names1, binders1, tc) ->
              let uu____29943 = FStar_Util.right tc in
              (univ_names1, binders1, uu____29943)
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1 ->
    fun s ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univ_names, binders, typ, lids, lids') ->
          let uu____29985 = elim_uvars_aux_t env1 univ_names binders typ in
          (match uu____29985 with
           | (univ_names1, binders1, typ1) ->
               let uu___3642_30025 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3642_30025.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3642_30025.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3642_30025.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3642_30025.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3642_30025.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
          let uu___3648_30040 = s in
          let uu____30041 =
            let uu____30042 =
              let uu____30051 = FStar_List.map (elim_uvars env1) sigs in
              (uu____30051, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____30042 in
          {
            FStar_Syntax_Syntax.sigel = uu____30041;
            FStar_Syntax_Syntax.sigrng =
              (uu___3648_30040.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3648_30040.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3648_30040.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3648_30040.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3648_30040.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univ_names, typ, lident, i, lids) ->
          let uu____30070 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____30070 with
           | (univ_names1, uu____30094, typ1) ->
               let uu___3662_30116 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3662_30116.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3662_30116.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3662_30116.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3662_30116.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3662_30116.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) ->
          let uu____30123 = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu____30123 with
           | (univ_names1, uu____30147, typ1) ->
               let uu___3673_30169 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3673_30169.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3673_30169.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3673_30169.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3673_30169.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3673_30169.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu____30199 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____30199 with
                    | (opening, lbunivs) ->
                        let elim t =
                          let uu____30224 =
                            let uu____30225 =
                              let uu____30226 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env1 uu____30226 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30225 in
                          elim_delayed_subst_term uu____30224 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___3689_30229 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3689_30229.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3689_30229.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3689_30229.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3689_30229.FStar_Syntax_Syntax.lbpos)
                        })) in
          let uu___3692_30230 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3692_30230.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3692_30230.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3692_30230.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3692_30230.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3692_30230.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l, us, t) ->
          let uu____30239 = elim_uvars_aux_t env1 us [] t in
          (match uu____30239 with
           | (us1, uu____30263, t1) ->
               let uu___3703_30285 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3703_30285.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3703_30285.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3703_30285.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3703_30285.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3703_30285.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30287 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit in
          (match uu____30287 with
           | (univs, binders, uu____30306) ->
               let uu____30327 =
                 let uu____30332 = FStar_Syntax_Subst.univ_var_opening univs in
                 match uu____30332 with
                 | (univs_opening, univs1) ->
                     let uu____30355 =
                       FStar_Syntax_Subst.univ_var_closing univs1 in
                     (univs_opening, uu____30355) in
               (match uu____30327 with
                | (univs_opening, univs_closing) ->
                    let uu____30358 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____30364 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____30365 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____30364, uu____30365) in
                    (match uu____30358 with
                     | (b_opening, b_closing) ->
                         let n = FStar_List.length univs in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____30391 =
                           match uu____30391 with
                           | (us, t) ->
                               let n_us = FStar_List.length us in
                               let uu____30409 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____30409 with
                                | (us1, t1) ->
                                    let uu____30420 =
                                      let uu____30429 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____30434 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____30429, uu____30434) in
                                    (match uu____30420 with
                                     | (b_opening1, b_closing1) ->
                                         let uu____30457 =
                                           let uu____30466 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           let uu____30471 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           (uu____30466, uu____30471) in
                                         (match uu____30457 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30495 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30495 in
                                              let uu____30496 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2 in
                                              (match uu____30496 with
                                               | (uu____30523, uu____30524,
                                                  t3) ->
                                                   let t4 =
                                                     let uu____30547 =
                                                       let uu____30548 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30548 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30547 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____30557 =
                             elim_uvars_aux_t env1 univs binders t in
                           match uu____30557 with
                           | (uu____30576, uu____30577, t1) -> t1 in
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
                             | uu____30653 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____30680 =
                               let uu____30681 =
                                 FStar_Syntax_Subst.compress body in
                               uu____30681.FStar_Syntax_Syntax.n in
                             match uu____30680 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,
                                  (FStar_Util.Inl typ,
                                   FStar_Pervasives_Native.None),
                                  FStar_Pervasives_Native.None)
                                 -> (defn, typ)
                             | uu____30740 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____30774 =
                               let uu____30775 =
                                 FStar_Syntax_Subst.compress t in
                               uu____30775.FStar_Syntax_Syntax.n in
                             match uu____30774 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars, body, uu____30798) ->
                                 let uu____30823 = destruct_action_body body in
                                 (match uu____30823 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu____30872 ->
                                 let uu____30873 = destruct_action_body t in
                                 (match uu____30873 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu____30928 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____30928 with
                           | (action_univs, t) ->
                               let uu____30937 = destruct_action_typ_templ t in
                               (match uu____30937 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      let uu___3787_30984 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3787_30984.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3787_30984.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3790_30986 = ed in
                           let uu____30987 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature in
                           let uu____30988 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu____30989 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3790_30986.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3790_30986.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____30987;
                             FStar_Syntax_Syntax.combinators = uu____30988;
                             FStar_Syntax_Syntax.actions = uu____30989;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3790_30986.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let uu___3793_30992 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3793_30992.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3793_30992.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3793_30992.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3793_30992.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3793_30992.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31013 =
            match uu___19_31013 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu____31044 = elim_uvars_aux_t env1 us [] t in
                (match uu____31044 with
                 | (us1, uu____31076, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___3808_31107 = sub_eff in
            let uu____31108 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____31111 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___3808_31107.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3808_31107.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31108;
              FStar_Syntax_Syntax.lift = uu____31111
            } in
          let uu___3811_31114 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3811_31114.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3811_31114.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3811_31114.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3811_31114.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3811_31114.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, univ_names, binders, comp, flags) ->
          let uu____31124 = elim_uvars_aux_c env1 univ_names binders comp in
          (match uu____31124 with
           | (univ_names1, binders1, comp1) ->
               let uu___3824_31164 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3824_31164.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3824_31164.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3824_31164.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3824_31164.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3824_31164.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31167 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31168 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31181 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m, n, p, (us_t, t), (us_ty, ty)) ->
          let uu____31211 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____31211 with
           | (us_t1, uu____31235, t1) ->
               let uu____31257 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____31257 with
                | (us_ty1, uu____31281, ty1) ->
                    let uu___3851_31303 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3851_31303.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3851_31303.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3851_31303.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3851_31303.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3851_31303.FStar_Syntax_Syntax.sigopts)
                    }))
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          (m, n, (us_t, t), (us_ty, ty)) ->
          let uu____31334 = elim_uvars_aux_t env1 us_t [] t in
          (match uu____31334 with
           | (us_t1, uu____31358, t1) ->
               let uu____31380 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu____31380 with
                | (us_ty1, uu____31404, ty1) ->
                    let uu___3871_31426 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                           (m, n, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3871_31426.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3871_31426.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3871_31426.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3871_31426.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3871_31426.FStar_Syntax_Syntax.sigopts)
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
        let uu____31477 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu____31477 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31499 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
            (match uu____31499 with
             | (uu____31506, head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     t.FStar_Syntax_Syntax.pos in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env1 t' in
                 FStar_Pervasives_Native.Some t'1) in
      let uu____31510 = FStar_Syntax_Util.head_and_args t in
      match uu____31510 with
      | (head, args) ->
          let uu____31555 =
            let uu____31556 = FStar_Syntax_Subst.compress head in
            uu____31556.FStar_Syntax_Syntax.n in
          (match uu____31555 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31563;
                  FStar_Syntax_Syntax.vars = uu____31564;_},
                us)
               -> aux fv us args
           | uu____31570 -> FStar_Pervasives_Native.None)
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
          let uu____31633 = FStar_Syntax_Util.arrow_formals_comp t1 in
          match uu____31633 with
          | (bs, c) ->
              let len = FStar_List.length bs in
              (match (bs, c) with
               | ([], uu____31669) when retry ->
                   let uu____31688 = unfold_whnf env1 t1 in
                   aux false n1 uu____31688
               | ([], uu____31690) when Prims.op_Negation retry -> (bs, c)
               | (bs1, c1) when len = n1 -> (bs1, c1)
               | (bs1, c1) when len > n1 ->
                   let uu____31758 = FStar_List.splitAt n1 bs1 in
                   (match uu____31758 with
                    | (bs_l, bs_r) ->
                        let uu____31825 =
                          let uu____31826 = FStar_Syntax_Util.arrow bs_r c1 in
                          FStar_Syntax_Syntax.mk_Total uu____31826 in
                        (bs_l, uu____31825))
               | (bs1, c1) when
                   ((len < n1) && (FStar_Syntax_Util.is_total_comp c1)) &&
                     (let uu____31852 = FStar_Syntax_Util.has_decreases c1 in
                      Prims.op_Negation uu____31852)
                   ->
                   let uu____31854 =
                     aux true (n1 - len) (FStar_Syntax_Util.comp_result c1) in
                   (match uu____31854 with
                    | (bs', c') -> ((FStar_List.append bs1 bs'), c'))
               | (bs1, c1) -> (bs1, c1)) in
        aux true n t